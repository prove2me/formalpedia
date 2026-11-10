-- Prove2me | Definitions.Def_MultiCollQ_FwdAlg
-- name    : MultiCollQ_FwdAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:15:28.755229+00:00
-- url     : https://prove2.me/theorems/192e0072-9012-439e-8c9e-c7717e4c6202
-- title:
--   Forward permutation-query algorithms, their real runs and compressed runs, witness and database probabilities
-- statement:
--   A **forward permutation-query algorithm** acts on an input register $X$ over $[N]$, a response register $W$ with basis $\{|\bot\rangle\}\cup\{|y\rangle:y\in[N]\}$, and further registers $A$ (output, auxiliary, the purified label assignment). It has a unit initial state and a unitary $U_j$ after the $j$-th query; inverse permutation access is excluded.
--
--   - **Real run.** For $\pi\in S_N$ each query is $P_\pi|x,w\rangle=|x\rangle\otimes S_{\pi(x)}|w\rangle$, where $S_y$ swaps $|\bot\rangle$ and $|y\rangle$.
--   - **Compressed run.** A database register $L$ with basis $\{|D\rangle : D$ a partial injection$\}$ starts in $|\emptyset\rangle$, and each query is $\mathrm{cpO}=\sum_x|x\rangle\langle x|\otimes Q_x$, $Q_x=(I_W\otimes C_x)U_x(I_W\otimes C_x)$ with $U_x=I_W\otimes Q_{x,\bot}+\sum_yS_y\otimes Q_{x,y}$ (Definition 2.3). The joint state after $s$ queries is $\zeta_s$, with $\zeta_{s+1}=U_{s+1}\,\mathrm{cpO}\,\zeta_s$.
--
--   For an output map sending each measurement outcome of the accessible registers to a list of input–output pairs and a set $B$ of partial injections:
--
--   - the **witness probability** $p$ is the probability, over a uniform $\pi$ and the final measurement of the real run, that every output pair $(x,y)$ has $\pi(x)=y$ and the partial injection they form ($\pi$ restricted to the listed inputs) lies in $B$;
--   - the **database probability** is $p_{\mathrm{db}}=\|P_B\zeta_T\|^2$, the probability that the final database lies in $B$.
--
--   **Formalization Note** The response register is `Option (Fin N)` with $\bot$ = `none`; the other registers are any finite type. The paper's $U_0$ before the first query is absorbed into the initial state; a run with $T$ queries uses $U_0,\dots,U_{T-1}$. The compressed query is the published `CompPermOracle.cpOCtl` (Carolan–Majenz, $\mathrm{cpO}_x=I\otimes C_xQ_{x,\bot}C_x^\dagger+\sum_yS_y\otimes C_xQ_{x,y}C_x^\dagger$), which equals $Q_x$ of (2.5) because $C_x$ is a self-adjoint unitary (p.20); the real query is `CompPermOracle.swapOracle`. The empty database is `⊥`.
-- source:
--   Peng, Hou, Dong, Quantum multi-collision lower bounds for arbitrary bounded types, manuscript (Oct. 2026; PDF sha256 e20a0870…), §2.3, Definition 2.3, (2.5), pp.11–12; Lemma 2.5, p.13; §2.4, p.14 (forward access only); p.22

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_swapOp
import Definitions.Def_CompPermOracle_cpO

namespace MultiCollQ

open CompPermOracle

/-- The accessible basis states of a forward permutation-query algorithm: a query input in `[N]`,
an answer in `W = [N] ∪ {⊥}`, and all remaining registers `A` (Peng, Hou, Dong, manuscript
(Oct. 2026), §2.3, p.11).

**Formalization Note.** `[N]` is `Fin N`; the response register `W` is `CompPermOracle.Ans N =
Option (Fin N)` with `⊥ = none`; the remaining registers (output, auxiliary, the purified label
assignment, …) are a finite type `Wk`. -/
abbrev FAcc (N : ℕ) (Wk : Type) := Fin N × Ans N × Wk

/-- An algorithm making **forward** permutation swap queries only (Peng, Hou, Dong, manuscript
(Oct. 2026), §2.3, p.11: "All query counts in this subsection refer to forward permutation swap
queries"; §2.4, p.14: "Inverse permutation access is excluded").

**Formalization Note.** A unit initial state on the accessible registers and a unitary `U j` on the
accessible registers after the query number `j` (counted from `0`); a run with `T` queries uses
`U 0, …, U (T−1)`. The oracle register (permutation or database) is not accessible: `U j` acts as
`U j ⊗ I` on it. Mid-circuit measurements are deferred and internal randomness purified into the
finite register `Wk`, so this is the paper's class of forward-query algorithms with arbitrary
auxiliary registers. -/
structure FwdAlg (N : ℕ) (Wk : Type) [Fintype Wk] where
  /-- The initial state on the accessible registers. -/
  init : Hil (FAcc N Wk)
  /-- It is a unit vector. -/
  norm_init : ‖init‖ = 1
  /-- The unitary applied after the query number `j`. -/
  U : ℕ → Hil (FAcc N Wk) ≃ₗᵢ[ℂ] Hil (FAcc N Wk)

variable {N : ℕ} {Wk : Type} [Fintype Wk] [DecidableEq Wk]

/-- The inter-query unitary as a bounded operator. -/
noncomputable def FwdAlg.Uop (A : FwdAlg N Wk) (j : ℕ) :
    Hil (FAcc N Wk) →L[ℂ] Hil (FAcc N Wk) :=
  (A.U j).toLinearIsometry.toContinuousLinearMap

/-- One real forward swap query `P_π|x, w⟩ = |x⟩ ⊗ S_{π(x)}|w⟩` (Peng, Hou, Dong, manuscript
(Oct. 2026), §2.3, p.12), i.e. `CompPermOracle.swapOracle π` on (input, answer), with the other
registers untouched. -/
noncomputable def realStep (π : Equiv.Perm (Fin N)) (ψ : Hil (FAcc N Wk)) : Hil (FAcc N Wk) :=
  WithLp.toLp 2 fun c =>
    swapOracle π (WithLp.toLp 2 fun p : Fin N × Ans N => ψ (p.1, p.2, c.2.2)) (c.1, c.2.1)

/-- The state of the algorithm against the permutation `π` after `j` queries, each followed by its
unitary. -/
noncomputable def FwdAlg.realState (A : FwdAlg N Wk) (π : Equiv.Perm (Fin N)) :
    ℕ → Hil (FAcc N Wk)
  | 0 => A.init
  | j + 1 => A.Uop j (realStep π (A.realState π j))

/-- One compressed forward query `cpO = Σ_x |x⟩⟨x| ⊗ Q_x` on (input, answer, database `L`), with
the other accessible registers untouched (Peng, Hou, Dong, manuscript (Oct. 2026), Definition 2.3,
(2.5), p.12).

**Formalization Note.** The operator is `CompPermOracle.cpOCtl` (Carolan–Majenz, Definition 3.6),
`cpO_x = I ⊗ M_{x,⊥} + Σ_y S_y ⊗ M_{x,y}` with `M = C_x Q C_x†`. Since `C_x` is a self-adjoint
unitary (p.20), this is `(I_W ⊗ C_x) U_x (I_W ⊗ C_x)` with
`U_x = I_W ⊗ Q_{x,⊥} + Σ_y S_y ⊗ Q_{x,y}`, the paper's `Q_x` of (2.5). -/
noncomputable def cpStep (ψ : Hil (FAcc N Wk × PartialPerm N)) : Hil (FAcc N Wk × PartialPerm N) :=
  WithLp.toLp 2 fun c =>
    cpOCtl (WithLp.toLp 2 fun p : Fin N × (Ans N × PartialPerm N) =>
        ψ ((p.1, p.2.1, c.1.2.2), p.2.2))
      (c.1.1, c.1.2.1, c.2)

/-- The joint state `ζ_s` (accessible registers ⊗ database) of the algorithm after `s` compressed
queries, each followed by its unitary: `ζ_0 = init ⊗ |∅⟩` and `ζ_{s+1} = (U_s ⊗ I) cpO ζ_s`
(Peng, Hou, Dong, manuscript (Oct. 2026), Definition 2.3, p.12; p.22).

**Formalization Note.** The empty database `∅` is `⊥ : PEquiv (Fin N) (Fin N)`. The paper's
`U_0` before the first query is absorbed into `init`. -/
noncomputable def FwdAlg.compressedState (A : FwdAlg N Wk) : ℕ → Hil (FAcc N Wk × PartialPerm N)
  | 0 => ketTensor A.init (ket ⊥)
  | j + 1 => opTensor (A.Uop j) (1 : Hil (PartialPerm N) →L[ℂ] Hil (PartialPerm N))
      (cpStep (A.compressedState j))

/-- The partial injection formed by a list of input–output pairs that agree with `π`: the
restriction of `π` to the inputs listed (Peng, Hou, Dong, manuscript (Oct. 2026), Lemma 2.5,
p.13: the pairs "after removing duplicates, form a partial injection"). -/
noncomputable def pairsPInj (π : Equiv.Perm (Fin N)) (L : List (Fin N × Fin N)) : PartialPerm N := by
  classical
  exact (PEquiv.ofSet {x | ∃ y, (x, y) ∈ L}).trans π.toPEquiv

/-- The real witness probability `p` of Lemma 2.5 (Peng, Hou, Dong, manuscript (Oct. 2026), p.13):
for a uniformly random permutation `π`, after `T` real forward queries the accessible registers are
measured in the computational basis and `out` of the outcome is the output list of pairs; `p` is
the probability that every pair agrees with `π` and the partial injection they form lies in `B`. -/
noncomputable def FwdAlg.witnessProb (A : FwdAlg N Wk) (T : ℕ) (out : FAcc N Wk → List (Fin N × Fin N))
    (B : Set (PartialPerm N)) : ℝ := by
  classical
  exact ((N.factorial : ℝ))⁻¹ * ∑ π : Equiv.Perm (Fin N),
    ∑ c ∈ Finset.univ.filter (fun c => (∀ p ∈ out c, π p.1 = p.2) ∧ pairsPInj π (out c) ∈ B),
      ‖A.realState π T c‖ ^ 2

/-- The database probability `p_db = ‖P_B ζ_T‖²` that the final database after `T` compressed
queries belongs to `B` (Peng, Hou, Dong, manuscript (Oct. 2026), §2.2, p.11; Lemma 2.5, p.13). -/
noncomputable def FwdAlg.dbProb (A : FwdAlg N Wk) (T : ℕ) (B : Set (PartialPerm N)) : ℝ := by
  classical
  exact ∑ c, ∑ D ∈ Finset.univ.filter (fun D : PartialPerm N => D ∈ B), ‖A.compressedState T (c, D)‖ ^ 2

end MultiCollQ


