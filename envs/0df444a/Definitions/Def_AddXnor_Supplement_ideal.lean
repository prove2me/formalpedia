-- Prove2me | Definitions.Def_AddXnor_Supplement_ideal
-- name    : AddXnor_Supplement_ideal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T01:30:45.374561+00:00
-- url     : https://prove2.me/theorems/9750ee9a-3fff-441c-8462-eaf619060323
-- title:
--   Ideal-chain planted-search permutation-oracle experiment
-- statement:
--   An **ideal chain** of depth $q$ on $m$-bit states consists of two independent uniform permutations $\pi_{i,0},\pi_{i,1}$ at every level. A query may evaluate either a permutation or its inverse. An adaptive oracle tree making at most $T$ queries receives $s_0$ and the planted target
--   $$
--   t=\pi_{q,x_q^*}\circ\cdots\circ\pi_{1,x_1^*}(s_0)
--   $$
--   and succeeds when its output labels any path from $s_0$ to $t$.
--
--   The planted success probability averages exactly over the independent permutations, the initial state, the planted path, and an arbitrary finite random-seed law for the adversary.
--
--   **Formalization Note** Internal computation is free, as in a query-complexity model. Forward and inverse queries both consume one level of the oracle tree. Levels are 0-based in Lean.
-- source:
--   Wang, Lv, Shen, Zhang, Add/XNOR Chains: An NP-Complete Boolean–Arithmetic Problem at the Meet-in-the-Middle Barrier, manuscript (sha256 405d6dda…), Section 6.1, pp.24–25 (PDF pp.24–25)

import Mathlib
import Definitions.Def_AddXnor_Supplement_core

set_option autoImplicit false

namespace AddXnor.Supplement

/-!
# Ideal-chain planted search model

This is the oracle model of Wang--Lv--Shen--Zhang, *Add/XNOR Chains* (manuscript,
sha256 405d6dda..., Section 6.1, pp.24--25, PDF pp.24--25).  It is deliberately separate from
the arithmetic Add/XNOR step: every `(level, operator)` pair is an independent permutation.
-/

/-- The `2q` permutations of an ideal `q`-level chain on `m`-bit states. -/
abbrev IdealFamily (q m : ℕ) := Fin q → Bool → Equiv.Perm (BitVec m)

/-- A forward or inverse oracle query.  `inverse=false` asks for `π_{i,b}(state)`;
`inverse=true` asks for `π_{i,b}^{-1}(state)`. -/
structure IdealQuery (q m : ℕ) where
  level : Fin q
  op : Bool
  inverse : Bool
  state : BitVec m

/-- Answer one ideal-chain oracle query. -/
def answerQuery {q m : ℕ} (π : IdealFamily q m) (Q : IdealQuery q m) : BitVec m :=
  if Q.inverse then (π Q.level Q.op).symm Q.state else π Q.level Q.op Q.state

/-- A deterministic adaptive oracle strategy making at most `T` queries.  Internal computation
is free, exactly as in the paper's query model. -/
inductive OracleTree (q m : ℕ) : ℕ → Type
  | output {T : ℕ} (x : Fin q → Bool) : OracleTree q m T
  | query {T : ℕ} (Q : IdealQuery q m)
      (next : BitVec m → OracleTree q m T) : OracleTree q m (T + 1)

/-- Run a deterministic oracle tree against a fixed ideal family. -/
def runOracleTree {q m T : ℕ} (π : IdealFamily q m) :
    OracleTree q m T → (Fin q → Bool)
  | .output x => x
  | .query Q next => runOracleTree π (next (answerQuery π Q))

/-- Composition `Π_x(s₀)=π_{q,x_q}∘...∘π_{1,x_1}(s₀)`, with 0-based levels in Lean. -/
def idealEval {q m : ℕ} (π : IdealFamily q m) (s₀ : BitVec m)
    (x : Fin q → Bool) : BitVec m :=
  (List.ofFn fun i : Fin q => (i, x i)).foldl (fun s ib => π ib.1 ib.2 s) s₀

/-- An arbitrary probability law on a finite random-seed type. -/
structure FiniteLaw (R : Type*) [Fintype R] where
  mass : R → ℝ
  nonneg : ∀ r, 0 ≤ mass r
  total : ∑ r, mass r = 1

/-- Success probability in the planted search experiment: sample every permutation uniformly
and independently, sample `s₀` and `x*` uniformly, set `t=Π_{x*}(s₀)`, sample the adversary's
finite random seed from `law`, then accept iff its output reaches the same `t`.

The function-space uniform law gives independence of all `2q` permutations. -/
noncomputable def plantedSuccess {q m T : ℕ} {R : Type*} [Fintype R] [Nonempty R]
    (law : FiniteLaw R)
    (adv : R → BitVec m → BitVec m → OracleTree q m T) : ℝ :=
  uniformMean fun π : IdealFamily q m =>
    uniformMean fun s₀ : BitVec m =>
      uniformMean fun xstar : Fin q → Bool =>
        ∑ r, law.mass r *
          if idealEval π s₀ (runOracleTree π (adv r s₀ (idealEval π s₀ xstar))) =
              idealEval π s₀ xstar then 1 else 0

end AddXnor.Supplement


