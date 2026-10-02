-- Prove2me | Definitions.Def_LeblSCV_Bergman_bergmanKernel
-- name    : LeblSCV_Bergman_bergmanKernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T09:56:45.063737+00:00
-- url     : https://prove2.me/theorems/8a7d1abd-99bc-477a-8258-a130d057e1d9
-- title:
--   The Bergman kernel $K_U(z, \bar\zeta) = \overline{k_z(\zeta)}$
-- statement:
--   Let $U \subset \mathbb{C}^n$ and $z \in \mathbb{C}^n$. An element $k_z \in A^2(U)$ **represents evaluation at $z$** if
--   $$f(z) = \langle f, k_z \rangle = \int_U f(\zeta)\, \overline{k_z(\zeta)} \, dV(\zeta) \qquad \text{for all } f \in A^2(U).$$
--   Such an element is unique if it exists; for $z$ in a domain $U$ it exists by Lemma 5.2.1 and the Riesz representation theorem (if it did not exist, $k_z$ is taken to be $0$). The **Bergman kernel** of $U$ is
--   $$K_U(z, \bar\zeta) = \overline{k_z(\zeta)},$$
--   defined for $(z, \bar\zeta) \in U \times U^*$, where $U^* = \{\zeta \in \mathbb{C}^n : \bar\zeta \in U\}$.
--
--   With this kernel every $f \in A^2(U)$ satisfies the reproducing property $f(z) = \int_U f(\zeta) K_U(z, \bar\zeta)\, dV(\zeta)$ (Eq. (5.1)).
--
--   **Formalization Note.** `bergmanRepresenter U z` is $k_z$, chosen by `Classical.choose` among the elements satisfying the displayed identity (with fallback $0$). `bergmanKernel U z ζ` is the book's $K_U(z, \bar\zeta)$: its **second argument is $\zeta$, not $\bar\zeta$**. The book's domain $(z, \bar\zeta) \in U \times U^*$ is therefore $(z, \zeta) \in U \times U$ in Lean. The integrand in the defining identity is the product of two $L^2(U)$ functions and hence always integrable.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 162 (definition of the Bergman kernel)

import Mathlib
import Definitions.Def_LeblSCV_Bergman_holoRep

open MeasureTheory

namespace LeblSCV.Bergman

open Classical in
/-- The element `k_z ∈ A²(U)` representing point evaluation at `z` (Lebl, p. 162):
`f(z) = ⟨f, k_z⟩ = ∫_U f(ζ) \overline{k_z(ζ)} dV(ζ)` for every `f ∈ A²(U)`. The book obtains it
from Lemma 5.2.1 and the Riesz representation theorem; it is unique when it exists. If no such
element exists the value is `0` (this never happens for `z` in a domain `U`, but proving that is
the content of Lemma 5.2.1 and the reproducing property (5.1)). -/
noncomputable def bergmanRepresenter {n : ℕ} (U : Set (Fin n → ℂ)) (z : Fin n → ℂ) :
    bergmanSpace U :=
  if h : ∃ k : bergmanSpace U, ∀ f : bergmanSpace U,
      holoRep U f z = ∫ ζ in U, holoRep U f ζ * (starRingEnd ℂ) (holoRep U k ζ) then
    h.choose
  else 0

/-- The Bergman kernel of `U` (Lebl, p. 162): `bergmanKernel U z ζ` is the book's
`K_U(z, ζ̄) = \overline{k_z(ζ)}`. The second argument is `ζ` itself, not `ζ̄`; the book's
domain `(z, ζ̄) ∈ U × U*`, `U* = {ζ : ζ̄ ∈ U}`, is `(z, ζ) ∈ U × U` here. -/
noncomputable def bergmanKernel {n : ℕ} (U : Set (Fin n → ℂ)) (z ζ : Fin n → ℂ) : ℂ :=
  (starRingEnd ℂ) (holoRep U (bergmanRepresenter U z) ζ)

end LeblSCV.Bergman


