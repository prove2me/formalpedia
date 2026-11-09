-- Prove2me | Definitions.Def_LinfContractionFP_label
-- name    : LinfContractionFP_label
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:19:12.461315+00:00
-- url     : https://prove2.me/theorems/353d88bc-fa3a-4b1b-9062-4d70bb6daf06
-- title:
--   Label (Algorithm 4): Amplify with ThinLabel as Oracle
-- statement:
--   Label$(L,U;\tau,\varepsilon)$ runs $\mathrm{Amplify}(0,2\tau,0,n,n)$ with $n=2d$ coordinates (the faces of the box) and Oracle given by ThinLabel at precision $\eta=\gamma\varepsilon$, so that the Oracle accuracy is $\rho=\gamma\eta/8=\gamma^2\varepsilon/8$. A shift $b$ is realised by moving $U_j$ up by $b_{(j,+)}$ and $L_j$ down by $b_{(j,-)}$ (Remark 4, footnote 2). If Oracle admits defeat, Label returns the point ThinLabel returned; otherwise it returns the labeling ($-1$ is $\mathsf{lo}$, $+1$ is $\mathsf{hi}$).
--
--   **Formalization Note** The recursive Solve calls inside ThinLabel are a parameter $\mathrm{solveSub}$. The cost counters of Amplify are discarded here.
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Algorithm 4, p.16; Remark 4 and footnote 2, p.11

import Mathlib
import Definitions.Def_LinfContractionFP_thinLabel
import Definitions.Def_LinfContractionFP_amplify

namespace LinfContractionFP

/-- Label(L, U; τ, ε) (Algorithm 4): `Amplify(0, 2τ, 0, n, n)` with `n = 2d` and Oracle given
by ThinLabel at precision `η = γε` on the shifted box (Remark 4), so that `ρ = γη/8 = γ²ε/8`.
Returns `Sum.inl x` (the point returned by ThinLabel when Oracle admits defeat) or `Sum.inr ℓ`
(the returned face labeling).

Soleymani–Farina, arXiv:2610.30122 (held version, sha256 595b4493…), Algorithm 4, p.16:
```
1 Have Oracle(b) be provided by ThinLabel (Remark 4) with desired precision η = γε;
2 Set n ← 2d;
3 Call Amplify(0, 2τ, 0, n, n);
4 if the call results in the oracle admitting defeat (i.e., returns a γε-approximate fixed
  point x) then
5   return x;          // This is an ε-near fixed point by Lemma 1
6 else
7   return the returned τ-accurate labeling;  // Label −1 is lo, label +1 is hi
```
and Remark 4 with footnote 2, p.11: "if the coordinate i corresponds to face (j, +), σ_i + b_i
can be induced by moving U_j up by b_i. If coordinate i corresponds to face (j, −), σ_i + b_i is
induced by moving L_j down by b_i."

**Formalization Note.** The coordinates of the game are the faces `ι × Bool`; the shift `b`
moves `L_j` down by `b(j, −)` and `U_j` up by `b(j, +)`. The recursive solves inside ThinLabel
are the parameter `solveSub`. This Oracle is stateless (it ignores the call
index). The cost counters of `amplifyRun` are discarded here. -/
noncomputable def label {ι : Type} [Fintype ι] (γ : ℝ) (f : (ι → ℝ) → (ι → ℝ))
    (solveSub : (S : Finset ι) → ((↥S → ℝ) → (↥S → ℝ)) → ℝ → (↥S → ℝ))
    (L U : ι → ℝ) (τ ε : ℝ) : (ι → ℝ) ⊕ (ι × Bool → Lbl) :=
  let η := γ * ε
  let O : ℕ → (ι × Bool → ℝ) → (ι → ℝ) ⊕ (ι × Bool → Lbl) := fun _ b =>
    thinLabel γ f solveSub (fun j => L j - b (j, false)) (fun j => U j + b (j, true)) η
  let n : ℝ := Fintype.card (ι × Bool)
  (amplifyRun O (γ * η / 8) 0 (2 * τ) 0 n n).1

end LinfContractionFP


