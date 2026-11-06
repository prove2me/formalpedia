-- Prove2me | Definitions.Def_TIESched_IsCompatibleIntegration
-- name    : TIESched_IsCompatibleIntegration
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:44:30.49256+00:00
-- url     : https://prove2.me/theorems/373aebd3-6ced-4466-91c8-6f5bc506e1dd
-- title:
--   Compatible positive integration $I_D$ (properties of Lemma A.1)
-- statement:
--   A family of real functionals $I_D$, $D\in\mathbb N$, defined on all bounded compactly supported real functions on $\mathbb R^D$ (measurable or not), is a **compatible positive integration** if:
--
--   1. *Linearity:* $I_D(ah+bg)=aI_D(h)+bI_D(g)$;
--   2. *Positivity:* $h\ge0$ pointwise implies $I_D(h)\ge0$;
--   3. *Translation invariance:* $I_D(s\mapsto h(s+a))=I_D(h)$ for all $a\in\mathbb R^D$;
--   4. *Agreement with ordinary integration:* $I_D(h)=\int_{\mathbb R^D}h(s)\,ds$ for continuous compactly supported $h$, and $I_D(\mathbf 1_B)=\mathrm{vol}(B)$ for every bounded box $B$, with any choice of endpoints;
--   5. *Compatibility across coordinate subsets:* in an average with a normalized product kernel, deleting coordinates on which the averaged function does not depend gives the same average on the remaining coordinates, in their inherited order.
--
--   These functionals replace the smoothing integrals of §5.4 for possibly non-measurable mechanisms.
--
--   **Formalization Note.** In 5, the remaining coordinates are the image of an order embedding $e:[D']\hookrightarrow[D]$, the averaged function is $s\mapsto f(s\circ e)$, and the kernel is $\prod_\ell k_\ell(s_\ell)$ with each factor continuous, compactly supported and of integral one; the identity is required whenever the reduced integrand is in the domain.
-- source:
--   Wang, Xu, Zhang, Tight Analysis of Randomized Truthful Scheduling: An (m+1)/2 Lower Bound, arXiv:2611.05142 (artifact sha256 a89db2da…), Lemma A.1, p.39

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace TIESched

/-- A **bounded compactly supported** real function on `ℝ^D` (the domain of the functionals `I_D`
of Lemma A.1, arXiv:2611.05142, p.39). No measurability is required. -/
def IsBCS {D : ℕ} (h : (Fin D → ℝ) → ℝ) : Prop :=
  (∃ C : ℝ, ∀ s, |h s| ≤ C) ∧ HasCompactSupport h

/-- A **bounded box** in `ℝ^D` "with any choice of endpoints" (Lemma A.1 (4), p.39): a product of
intervals with endpoints `a_ℓ, b_ℓ`, each open, closed or half-open. -/
def IsBox {D : ℕ} (B : Set (Fin D → ℝ)) : Prop :=
  ∃ (a b : Fin D → ℝ) (I : Fin D → Set ℝ),
    (∀ l, I l = Set.Ioo (a l) (b l) ∨ I l = Set.Ico (a l) (b l) ∨ I l = Set.Ioc (a l) (b l) ∨
      I l = Set.Icc (a l) (b l)) ∧ B = Set.univ.pi I

/-- **Compatible positive integration** (arXiv:2611.05142, Lemma A.1, p.39): a family of real
functionals `I_D` on bounded compactly supported real functions on `ℝ^D`, `D ∈ ℕ`, with

1. *Linearity:* `I_D(ah + bg) = a I_D(h) + b I_D(g)`;
2. *Positivity:* `h ≥ 0` pointwise implies `I_D(h) ≥ 0`;
3. *Translation invariance:* `I_D(s ↦ h(s + a)) = I_D(h)` for every `a ∈ ℝ^D`;
4. *Agreement with ordinary integration:* `I_D(h) = ∫_{ℝ^D} h(s) ds` for continuous compactly
   supported `h`, and `I_D(1_B) = vol(B)` for every bounded box `B`, with any choice of endpoints;
5. *Compatibility across coordinate subsets:* in an average with a normalized product kernel,
   deleting coordinates on which the averaged function does not depend gives the same average on
   the remaining coordinates, in their inherited order.

**Formalization Note.** Properties 1–3 quantify over bounded compactly supported `h, g` (`IsBCS`);
the values of `I_D` elsewhere are unconstrained. In 5, the remaining coordinates are the image of an
order embedding `e : Fin D' ↪o Fin D` (the inherited order); the averaged function is
`s ↦ f(s ∘ e)`; the normalized product kernel is `∏_ℓ k_ℓ(s_ℓ)` with each factor continuous,
compactly supported and of integral one; the identity is required whenever the reduced integrand
lies in the domain. -/
def IsCompatibleIntegration (I : (D : ℕ) → ((Fin D → ℝ) → ℝ) → ℝ) : Prop :=
  (∀ (D : ℕ) (h g : (Fin D → ℝ) → ℝ) (a b : ℝ), IsBCS h → IsBCS g →
      I D (fun s => a * h s + b * g s) = a * I D h + b * I D g) ∧
  (∀ (D : ℕ) (h : (Fin D → ℝ) → ℝ), IsBCS h → (∀ s, 0 ≤ h s) → 0 ≤ I D h) ∧
  (∀ (D : ℕ) (h : (Fin D → ℝ) → ℝ) (a : Fin D → ℝ), IsBCS h → I D (fun s => h (s + a)) = I D h) ∧
  (∀ (D : ℕ) (h : (Fin D → ℝ) → ℝ), Continuous h → HasCompactSupport h → I D h = ∫ s, h s) ∧
  (∀ (D : ℕ) (B : Set (Fin D → ℝ)), IsBox B → I D (B.indicator 1) = (volume B).toReal) ∧
  (∀ (D D' : ℕ) (e : Fin D' ↪o Fin D) (f : (Fin D' → ℝ) → ℝ) (k : Fin D → ℝ → ℝ),
      (∀ l, Continuous (k l)) → (∀ l, HasCompactSupport (k l)) → (∀ l, ∫ t, k l t = 1) →
      IsBCS (fun s' : Fin D' → ℝ => f s' * ∏ l', k (e l') (s' l')) →
      I D (fun s => f (fun l' => s (e l')) * ∏ l, k l (s l)) =
        I D' (fun s' => f s' * ∏ l', k (e l') (s' l')))

end TIESched


