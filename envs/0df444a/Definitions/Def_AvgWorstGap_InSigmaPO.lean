-- Prove2me | Definitions.Def_AvgWorstGap_InSigmaPO
-- name    : AvgWorstGap_InSigmaPO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:45:57.972338+00:00
-- url     : https://prove2.me/theorems/efa482ca-54cd-4af3-82ce-1a3a69db5e3d
-- title:
--   $\Sigma_k^{\mathrm P,O}$, $\mathsf{NP}^O$, $\mathsf{NP}$ and $\mathsf{PH}$
-- statement:
--   A language $L$ is in $\Sigma_k^{\mathrm P,O}$ if there are a deterministic polynomial-time verifier $V$ with oracle $O$ and a polynomial $v$ such that for every $x$ of length $n$,
--   $$x\in L\iff \exists y_1\in\{0,1\}^{v(n)}\ \forall y_2\in\{0,1\}^{v(n)}\cdots Q_ky_k\in\{0,1\}^{v(n)}:\ V(x,y_1,\dots,y_k)=1.$$
--   $V$ must halt within a polynomial in its input length, with a one-bit output, on every input. Then $\Sigma_k^{\mathrm P}=\Sigma_k^{\mathrm P,\emptyset}$, $\mathsf{NP}^O=\Sigma_1^{\mathrm P,O}$, $\mathsf{NP}=\Sigma_1^{\mathrm P}$, and $\mathsf{PH}=\bigcup_{k\ge0}\Sigma_k^{\mathrm P}$.
--
--   **Formalization Note** The tuple $(x,y_1,\dots,y_k)$ is given to $V$ through the tuple encoding. $k=0$ gives $\mathsf P^O$.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), proof of Lemma 3.14, p.28 (alternating-quantifier form)

import Mathlib
import Definitions.Def_AvgWorstGap_InPrBPP
import Definitions.Def_NKtLB_tupleEnc
import Definitions.Def_AvgWorstGap_pairStr

namespace AvgWorstGap

open NKtLB

/-- **Alternating quantifiers** over `k` strings of length `v`: `altQ k true v P` is
`∃y₁ ∀y₂ ∃y₃ … P(y₁, …, y_k)` (`false` starts with `∀`). -/
def altQ : ℕ → Bool → ℕ → (List (List Bool) → Prop) → Prop
  | 0, _, _, P => P []
  | k + 1, true, v, P => ∃ y : List Bool, y.length = v ∧ altQ k false v (fun ys => P (y :: ys))
  | k + 1, false, v, P => ∀ y : List Bool, y.length = v → altQ k true v (fun ys => P (y :: ys))

/-- **A deterministic polynomial-time verifier with oracle `O`**: on every input `u` the machine
halts within `p(|u|)` steps with a one-bit output (auxiliary, guess and randomness tapes empty). -/
def IsPolyVerifier (O : Set (List Bool)) (V : Machine) (p : Polynomial ℕ) : Prop :=
  ∀ u : List Bool, ∃ b : Bool, V.HaltsWith O ⟨u, [], [], []⟩ (p.eval u.length) (bitOut b)

/-- **`Σ_k^{P,O}`** by alternating quantifiers (the form used in arXiv:2610.19162, version of
October 30, 2026, proof of Lemma 3.14, p.28): "`x ∈ L` if and only if `∃y1 ∈ {0, 1}^{v(n)},
∀y2 ∈ {0, 1}^{v(n)}, . . . , Qk yk ∈ {0, 1}^{v(n)}, V(x, y1, y2, . . . , yk) = 1`, where `v` is a
polynomial", with `V` deterministic polynomial-time (here with oracle `O`).

**Formalization Note.** The tuple `(x, y₁, …, y_k)` is `tupleEnc`; `V` runs within `p` of its input
length; `k = 0` gives `P^O`. -/
def InSigmaPO (O : Set (List Bool)) (k : ℕ) (L : Set (List Bool)) : Prop :=
  ∃ (V : Machine) (p v : Polynomial ℕ), IsPolyVerifier O V p ∧
    ∀ x : List Bool, x ∈ L ↔ altQ k true (v.eval x.length) (fun ys =>
      V.HaltsWith O ⟨tupleEnc (x :: ys), [], [], []⟩ (p.eval (tupleEnc (x :: ys)).length)
        (bitOut true))

/-- **`Σ_k^P`** (no oracle). -/
def InSigmaP (k : ℕ) (L : Set (List Bool)) : Prop := InSigmaPO ∅ k L

/-- **`NP^O`** `= Σ_1^{P,O}`. -/
def InNPO (O : Set (List Bool)) (L : Set (List Bool)) : Prop := InSigmaPO O 1 L

/-- **`NP`** `= Σ_1^P`. -/
def InNP (L : Set (List Bool)) : Prop := InNPO ∅ L

/-- **`PH`** `= ⋃_{k ≥ 0} Σ_k^P`. -/
def InPH (L : Set (List Bool)) : Prop := ∃ k : ℕ, InSigmaP k L

end AvgWorstGap


