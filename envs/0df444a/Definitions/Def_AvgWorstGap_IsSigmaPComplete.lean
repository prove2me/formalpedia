-- Prove2me | Definitions.Def_AvgWorstGap_IsSigmaPComplete
-- name    : AvgWorstGap_IsSigmaPComplete
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:47:07.955897+00:00
-- url     : https://prove2.me/theorems/8ac0cc45-8055-4f32-ad72-bdc0cd1dc906
-- title:
--   Polynomial-time many-one reductions, $\mathsf{NP}^O$-hardness and $\Sigma_k^{\mathrm P}$-completeness
-- statement:
--   A function $f$ is computed in time $p$ by a machine that halts within $p(|u|)$ steps with output $f(u)$ on every input $u$. $L_1$ **reduces** to $L_2$ if some polynomial-time computable $f$ satisfies $u\in L_1\iff f(u)\in L_2$ for all $u$.
--
--   - $L$ is **hard for $\mathsf{NP}^O$** if every language in $\mathsf{NP}^O$ is decided by a deterministic polynomial-time machine with oracle $L$ (Turing reductions; many-one hardness implies it).
--   - $L$ is **$\Sigma_k^{\mathrm P}$-complete** if $L\in\Sigma_k^{\mathrm P}$ and every language in $\Sigma_k^{\mathrm P}$ reduces to $L$.
--
--   The reductions in "reduces" and in completeness are deterministic polynomial-time many-one reductions; hardness for $\mathsf{NP}^O$ uses Turing reductions, as above.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), Lemma 2.17, p.17; Lemma 3.14, p.27

import Mathlib
import Definitions.Def_AvgWorstGap_InSigmaPO

namespace AvgWorstGap

open NKtLB

/-- **`M` computes `f` in time `p`**: on every input `u` (oracle `∅`, other tapes empty) it halts
within `p(|u|)` steps with output `f(u)`. -/
def ComputesFn (M : Machine) (p : Polynomial ℕ) (f : List Bool → List Bool) : Prop :=
  ∀ u : List Bool, M.HaltsWith ∅ ⟨u, [], [], []⟩ (p.eval u.length) (bitsSym (f u))

/-- **Deterministic polynomial-time many-one reduction** from `L₁` to `L₂`. -/
def ManyOneReduces (L₁ L₂ : Set (List Bool)) : Prop :=
  ∃ (M : Machine) (p : Polynomial ℕ) (f : List Bool → List Bool), ComputesFn M p f ∧
    ∀ u : List Bool, u ∈ L₁ ↔ f u ∈ L₂

/-- **`L` is hard for `NP^O` under deterministic polynomial-time reductions** (arXiv:2610.19162,
version of October 30, 2026, Lemma 2.17, p.17): every `L' ∈ NP^O` is decided by a deterministic
polynomial-time machine with oracle `L`, i.e. `L' ∈ P^L = Σ_0^{P,L}`.

**Formalization Note.** The paper does not say which kind of reduction; this is the Turing (oracle)
reading, the broadest one. Hardness under many-one reductions implies it, so a statement assuming
`IsNPOHard O L` covers the many-one reading as well. -/
def IsNPOHard (O L : Set (List Bool)) : Prop :=
  ∀ L' : Set (List Bool), InNPO O L' → InSigmaPO L 0 L'

/-- **`L` is `Σ_k^P`-complete** (Lemma 3.14, p.27): `L ∈ Σ_k^P` and every `Σ_k^P` language reduces
to it by a deterministic polynomial-time many-one reduction. -/
def IsSigmaPComplete (k : ℕ) (L : Set (List Bool)) : Prop :=
  InSigmaP k L ∧ ∀ L' : Set (List Bool), InSigmaP k L' → ManyOneReduces L' L

end AvgWorstGap


