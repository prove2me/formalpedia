-- Prove2me | Definitions.Def_NoisyOWMPC_SecErr
-- name    : NoisyOWMPC_SecErr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:54:37.448995+00:00
-- url     : https://prove2.me/theorems/0f520145-4a0a-4d64-980d-90a3b4a1d9c4
-- title:
--   Correctness, coalition security, Las Vegas and efficiency of one-way MPC
-- statement:
--   For a one-way protocol $\Pi$ over $\mathbf C$ (Definition 4.2):
--   1. **correctness error** $\varepsilon_{\mathrm{cor}}$: for every $\lambda$ and $x$, $\mathrm{SD}(\mathbf y,F(x))\le\varepsilon_{\mathrm{cor}}(\lambda)$;
--   2. **security error** $\varepsilon_T$ for the coalition $T=J$ or $T=\{S\}\cup J$: there is a PPT simulator $\mathrm{Sim}_T$ with
--   $$(x,\mathbf y_{-J},\mathrm{view}_T)\approx^c_{\varepsilon_T}(x,\bar{\mathbf y}_{-J},\mathrm{Sim}_T(1^\lambda,x_T,\bar{\mathbf y}_J)),$$
--   where $\bar{\mathbf y}\leftarrow F(x)$, $\mathrm{view}_S=(r_S,\tau,\hat{\mathbf x})$, $\mathrm{view}_i=(\tau,\hat{\mathbf y}_i)$, and $x_T$ is $x$ if $S\in T$ and $\perp$ otherwise;
--   3. **Las Vegas** (Definition 4.3): every output is $\mathsf{fail}$ or in the support of $f_i(x;\rho_i)$;
--   4. **efficiency**: $L$ and $N$ are polynomial, the sender is implementable in polynomial time within $2^{-\lambda}$, and each $R_i$ is deterministic polynomial time.
--
--   **Formalization Note** The simulator is fixed before the distinguisher and the input; tuples are encoded by the published tuple encoding.
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Definitions 4.2 and 4.3, pp.18–19

import Mathlib
import Definitions.Def_NoisyOWMPC_Protocol
import Definitions.Def_NoisyOWMPC_CompClose
import Definitions.Def_NoisyOWMPC_CoinAlg
import Definitions.Def_NoisyOWMPC_symEnc

namespace NoisyOWMPC

open LaconicBarrier

variable {k : ℕ} {X : Type} [Fintype X] {Y : Fin k → Type} [∀ i, Fintype (Y i)]
  {F : Functionality k}

/-- The encoding of the outputs `(o_i)_{i ∈ S}` of the receivers in a set `S`, in increasing order
of `i` (Ishai, Lu, Zafar, STOC 2027 submission (manuscript sha256 3a9569fa…), Definition 4.2, p.18:
"a subscript `J` selects those coordinates and a subscript `−J` omits them"). -/
def outsEnc {lo : Fin k → ℕ} (S : Fin k → Prop) [DecidablePred S]
    (o : ∀ i, Option (Fin (lo i) → Bool)) : List Bool :=
  QAdvFew.PoQOracle.tup ((List.finRange k).filterMap fun i => if S i then some (optEnc (o i)) else none)

/-- **Correctness error** `ε_cor` (Definition 4.2, p.19): for every `λ` and `x ∈ M`,
`SD(y, F(x)) ≤ ε_cor(λ)`, where `y` is the vector of decoded outputs and `F(x)` the ideal outputs
`(f_i(x; ρ_i))_i` with independent uniform `ρ_i`. -/
def Protocol.CorrErr (P : Protocol k X Y F) (C : ∀ i, DMC X (Y i)) (ε : ℕ → ℝ) : Prop :=
  ∀ lam (x : Fin (F.lx lam) → Bool),
    sdPush (P.realW C lam x) (fun ω => fun i => P.out lam x ω i)
      (unifW (∀ i, Fin (F.r i lam) → Bool)) (fun ρ => fun i => some (F.f lam i x (ρ i))) ≤ ε lam

/-- The encoding of the coalition's view `view_T` in the real execution, for the coalition `T = J`
(receivers) plus the sender if `withS` (Ishai, Lu, Zafar, STOC 2027 submission (manuscript sha256
3a9569fa…), Definition 4.2, p.18: "`view_S = (r_S, τ, x̂)` … `view_i = (τ, ŷ_i)` … the view `view_T`
comprise[s] `(view_i)_{i ∈ J}`, together with `view_S` if `S ∈ T`"). -/
noncomputable def Protocol.viewEnc (P : Protocol k X Y F) (withS : Bool) (J : Finset (Fin k))
    (lam : ℕ) (x : Fin (F.lx lam) → Bool) (ω : P.RS lam × (Fin (P.N lam) → ∀ i, Y i)) :
    List Bool :=
  QAdvFew.PoQOracle.tup ((if withS then [QAdvFew.PoQOracle.tup [P.encRS lam ω.1,
      bits (P.send lam x ω.1).1, wordEnc X (P.send lam x ω.1).2]] else []) ++
    (List.finRange k).filterMap fun i => if i ∈ J then
      some (QAdvFew.PoQOracle.tup [bits (P.send lam x ω.1).1, wordEnc (Y i) (fun p => ω.2 p i)])
      else none)

/-- The encoding of the real tuple `(x, y_{−J}, view_T)` (Definition 4.2, (4.1), p.19). -/
noncomputable def Protocol.realTuple (P : Protocol k X Y F) (withS : Bool) (J : Finset (Fin k))
    (lam : ℕ) (x : Fin (F.lx lam) → Bool) (ω : P.RS lam × (Fin (P.N lam) → ∀ i, Y i)) :
    List Bool :=
  QAdvFew.PoQOracle.tup [bits x, outsEnc (fun i => i ∉ J) (fun i => P.out lam x ω i),
    P.viewEnc withS J lam x ω]

/-- The encoding of the ideal tuple `(x, ȳ_{−J}, Sim_T(1^λ, x_T, ȳ_J))` with ideal coins `ρ` and
simulator coins `σ` (Definition 4.2, (4.1), p.19); `x_T` is `1x` if the sender is in `T` and `0`
(for `⊥`) otherwise. -/
def idealTuple (F : Functionality k) (Sim : CoinAlg) (withS : Bool) (J : Finset (Fin k)) (lam : ℕ)
    (x : Fin (F.lx lam) → Bool)
    (ω : (∀ i, Fin (F.r i lam) → Bool) × (Fin (Sim.coins lam) → Bool)) : List Bool :=
  QAdvFew.PoQOracle.tup [bits x,
    outsEnc (fun i => i ∉ J) (fun i => some (F.f lam i x (ω.1 i))),
    Sim.run lam (QAdvFew.PoQOracle.tup [if withS then true :: bits x else [false],
      outsEnc (fun i => i ∈ J) (fun i => some (F.f lam i x (ω.1 i)))]) ω.2]

/-- **Security error `ε_T` for the coalition `T`** (Definition 4.2, (4.1), p.19): there is a PPT
simulator `Sim_T` such that, for every `x ∈ M`,
`(x, y_{−J}, view_T) ≈^c_{ε_T} (x, ȳ_{−J}, Sim_T(1^λ, x_T, ȳ_J))`, where the ideal experiment
samples `ȳ ← F(x)`. The coalition is the receiver set `J` together with the sender if `withS`.

**Formalization Note** The simulator is fixed before the distinguisher and the input (§3, p.15);
the negligible term of `≈^c` is chosen before `λ` and `x` (`CompClose`). -/
def Protocol.SecErr (P : Protocol k X Y F) (C : ∀ i, DMC X (Y i)) (withS : Bool)
    (J : Finset (Fin k)) (ε : ℕ → ℝ) : Prop :=
  ∃ Sim : CoinAlg, Sim.IsPPT ∧
    CompClose (I := fun lam => Fin (F.lx lam) → Bool)
      (P.realW C) (P.realTuple withS J)
      (fun lam _ => unifW ((∀ i, Fin (F.r i lam) → Bool) × (Fin (Sim.coins lam) → Bool)))
      (idealTuple F Sim withS J) ε

/-- **Las Vegas** (Definition 4.3, p.19): for every input `x` and receiver `i`,
`supp(y_i) ⊆ supp(f_i(x; ρ_i)) ∪ {fail}`. -/
def Protocol.LasVegas (P : Protocol k X Y F) (C : ∀ i, DMC X (Y i)) : Prop :=
  ∀ lam (x : Fin (F.lx lam) → Bool) (ω : P.RS lam × (Fin (P.N lam) → ∀ i, Y i)),
    P.realW C lam x ω ≠ 0 → ∀ i, P.out lam x ω i = none ∨ ∃ ρ, P.out lam x ω i = some (F.f lam i x ρ)

/-- **Efficiency** of the protocol (Definition 4.2, p.18, and §3, p.15): the lengths `L`, `N` are
polynomially bounded; the sender is implementable in polynomial time within statistical distance
`2^{−λ}` (§5 Conventions, p.21), its output being its view `(r_S, τ, x̂)`; and each receiver `R_i`
is a deterministic polynomial-time algorithm. -/
def Protocol.IsEfficient (P : Protocol k X Y F) : Prop :=
  PolyBounded P.L ∧ PolyBounded P.N ∧
  Samplable (I := fun lam => Fin (F.lx lam) → Bool) (fun lam _ => P.wS lam)
    (fun lam x r => QAdvFew.PoQOracle.tup [P.encRS lam r, bits (P.send lam x r).1,
      wordEnc X (P.send lam x r).2]) (fun _ x => bits x) ∧
  ∀ i, PolyTimeOn (ι := (lam : ℕ) × (Fin (P.L lam) → Bool) × (Fin (P.N lam) → Y i))
    (fun z => [unary z.1, bits z.2.1, wordEnc (Y i) z.2.2]) (fun z => optEnc (P.recv z.1 i z.2.1 z.2.2))

end NoisyOWMPC


