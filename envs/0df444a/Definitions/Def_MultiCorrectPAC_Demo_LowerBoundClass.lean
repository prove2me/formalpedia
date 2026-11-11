-- Prove2me | Definitions.Def_MultiCorrectPAC_Demo_LowerBoundClass
-- name    : MultiCorrectPAC_Demo_LowerBoundClass
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:44:52.851537+00:00
-- url     : https://prove2.me/theorems/6272e693-5005-4eb2-872e-4204b4ee2be9
-- title:
--   The classes $\mathcal H_b$ of (59) on $[b]\times\mathbb N^\ell$ with labels $[\ell]$
-- statement:
--   Fix $\ell\ge2$ and an integer $b\ge1$. The instance space is $[b]\times\mathbb N^\ell$ ($\mathbb N=\{1,2,\dots\}$) and the label space is $[\ell]$. A target is given by $t=(t^{(1)},\dots,t^{(b)})\in(\mathbb N^\ell)^b$ and a finite set $F\subseteq[b]\times\mathbb N^\ell$:
--   $$f_F(j,x)=1+\mathbb 1\{(j,x)\in F\},\qquad h_{t,F}(j,x)=\{f_F(j,x)\}\cup\{i\in[\ell]:x_i\ne t^{(j)}_i\}.\tag{59}$$
--   $\mathcal H_b$ is the class of all $h_{t,F}$; it is a total class whose correct-label sets have at most $\ell$ labels.
--
--   **Formalization Note** $[b]$ is `Fin b`; $\mathbb N^\ell$ is `Fin ℓ → ℕ` (the paper's coordinate $s\ge1$ is the Lean value $s-1$); the label $i\in[\ell]$ is `⟨i-1, _⟩ : Fin ℓ`, so $f_F\in\{1,2\}$ is the index `0` or `1` (`if p ∈ F then 1 else 0`), and the label excluded on the slice $x_i=t^{(j)}_i$ is the index of coordinate $i$. `hbHyp ℓ b t F` builds the value set by filtering `Fin ℓ`, which for $\ell\ge2$ is exactly (59).
-- source:
--   Hanneke, Mansouri, Pour, Shaeiri, Wang, PAC Learning with Multiple Correct Answers, STOC 2027 submission (manuscript sha256 2844bd34…), p. 64 (PDF 66), (59)

import Mathlib
import Definitions.Def_MultiCorrectPAC_Demo_Hypotheses

namespace MultiCorrectPAC.Demo

/-! Hanneke, Mansouri, Pour, Shaeiri, Wang, *PAC Learning with Multiple Correct Answers*,
(59) (printed p. 64, PDF 66): the classes `H_b` of Theorem 43. The paper's instance space is
`[b] × ℕ^ℓ` with `ℕ = {1, 2, …}` and label space `[ℓ]`. Here `[b]` is `Fin b`, `ℕ^ℓ` is
`Fin ℓ → ℕ` (the paper's coordinate value `s ≥ 1` is the Lean value `s − 1`), and the label
`i ∈ [ℓ]` is `⟨i − 1, _⟩ : Fin ℓ`; so the binary label `f_F = 1 + 1{(j, x) ∈ F}` is the index
`0` or `1`, and the label of coordinate `i` is the index of that coordinate. -/

/-- `h_{t,F}(j, x) = {f_F(j, x)} ∪ {i ∈ [ℓ] : xᵢ ≠ t^{(j)}ᵢ}` of (59), with
`f_F(j, x) = 1 + 1{(j, x) ∈ F}`, for `t = (t^{(1)}, …, t^{(b)})` and a finite
`F ⊆ [b] × ℕ^ℓ`. For `ℓ ≥ 2` (the range of Theorem 43) the first part is the single label
`f_F(j, x)`. -/
def hbHyp (ℓ b : ℕ) (t : Fin b → Fin ℓ → ℕ) (F : Finset (Fin b × (Fin ℓ → ℕ))) :
    Hyp (Fin b × (Fin ℓ → ℕ)) (Fin ℓ) := fun p =>
  some (Finset.univ.filter fun i : Fin ℓ =>
    (i : ℕ) = (if p ∈ F then 1 else 0) ∨ p.2 i ≠ t p.1 i)

/-- The class `H_b = {h_{t,F} : t ∈ (ℕ^ℓ)^b, F ⊆ [b] × ℕ^ℓ finite}` of (59). -/
def classHb (ℓ b : ℕ) : Set (Hyp (Fin b × (Fin ℓ → ℕ)) (Fin ℓ)) :=
  {h | ∃ (t : Fin b → Fin ℓ → ℕ) (F : Finset (Fin b × (Fin ℓ → ℕ))), h = hbHyp ℓ b t F}

end MultiCorrectPAC.Demo


