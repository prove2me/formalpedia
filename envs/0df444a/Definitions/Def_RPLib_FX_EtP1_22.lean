-- Prove2me | Definitions.Def_RPLib_FX_EtP1_22
-- name    : RPLib_FX_EtP1_22
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T12:00:19.516264+00:00
-- url     : https://prove2.me/theorems/9315b109-b4fc-5f51-b3a8-88f360a0b638
-- title:
--   Étale cohomology of the projective line, library file 22 of 34
-- statement:
--   File 22 of 34 of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_MV`: S4-EtCompact: the Mayer-Vietoris sequence for a Zariski cover (O8c, file M1)
--   * `S4.Def_RP_EtCompact_P1H2`: S4-EtCompact: `H^2(P^1, Λ) ≃ Λ` and `H^2_c(A^1, Λ) ≃ Λ` (O8c, file M6)
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_21

/-!
# Étale cohomology of the projective line, library file 22 of 34

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_MV`: S4-EtCompact: the Mayer-Vietoris sequence for a Zariski cover (O8c, file M1)
* `S4.Def_RP_EtCompact_P1H2`: S4-EtCompact: `H^2(P^1, Λ) ≃ Λ` and `H^2_c(A^1, Λ) ≃ Λ` (O8c, file M6)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_MV =====
section

/-!
# S4-EtCompact: the Mayer-Vietoris sequence for a Zariski cover (O8c, file M1)

* `mvS F U V`: the short complex `j_{U⊓V!}F ⟶ j_{U!}F ⊞ j_{V!}F ⟶ F`; **`mvS_shortExact`** when `U ∪ V = X`.
* `subsingleton_ext_biprod`, **`precomp_extClass_bijective`**: `Ext` out of a biproduct; the connecting map of the
  contravariant `Ext` sequence is bijective when the middle terms vanish.
* `cutExt j G n : Ext^n(j_{U!}Λ_U, G) ≃ H^n(U, G|_U)`, `cutH j n`, `cutHOpen W n`.
* **`P1.h2Equiv`**: `H^2(P^1, Λ) ≃ H^1(U ⊓ V, Λ)` for the two standard charts, when `H^1(A^1, Λ) = H^2(A^1, Λ) = 0`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe w v u

section ExtGen

variable {C : Type v} [Category.{w} C] [Abelian C] [HasExt.{u} C]

end ExtGen

section MV

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

end MV

section Cut

variable {Λ : Type u} [CommRing Λ] {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]

end Cut

section CutOpen

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

end CutOpen

section ExtIface

variable {C : Type v} [Category.{w} C] [Abelian C]

variable [HasExt.{u} C]

end ExtIface

section P1

variable (K : Type u) [Field K] {Λ : Type u} [CommRing Λ]

/-- **`H^2(P^1, Λ) ≃ H^1(U ⊓ V, Λ)`** (Mayer-Vietoris on the two standard charts `U, V ≅ A^1`), when
`H^1(A^1, Λ) = H^2(A^1, Λ) = 0`. -/
def P1.h2Equiv (h1 : Subsingleton (H Λ (unitSh Λ (A1 K)) 1)) (h2 : Subsingleton (H Λ (unitSh Λ (A1 K)) 2)) :
    H Λ (unitSh Λ (P1 K)) 2 ≃+
      H Λ (unitSh Λ ((chartA1 K).opensRange ⊓ (chartA1' K).opensRange).toScheme) 1 :=
  (P1.e0G K h1 h2).trans (cutHOpen _ 1)

end P1

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_P1H2 =====
section

/-!
# S4-EtCompact: `H^2(P^1, Λ) ≃ Λ` and `H^2_c(A^1, Λ) ≃ Λ` (O8c, file M6)

`k` algebraically closed, `l` prime invertible in `k`, `lⁿ • Λ = 0` (`n > 0`).

* `A1.subsingleton_h2`: `H^2(A^1, Λ) = 0` (`H2Pid.H_A1_two_eq_zero`);
* **`P1.nonempty_h2Equiv`**: `H^2(P^1, Λ) ≃+ Λ` (Mayer-Vietoris `P1.h2EquivGm` + `Gm.nonempty_h1Equiv`);
* **`A1.nonempty_hc2Equiv`**: `H^2_c(A^1, Λ) ≃+ Λ` (`A1.hcEquivP1`).
-/

set_option autoImplicit false

open Polynomial AlgebraicGeometry

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

variable (k : Type) [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ] {l n : ℕ} [Fact l.Prime]

/-- `H^2(A^1_k, Λ) = 0`. -/
theorem A1.subsingleton_h2 (hl : (l : k) ≠ 0) (hΛ : ((l ^ n : ℕ) : Λ) = 0) :
    Subsingleton (H Λ (unitSh Λ (A1 k)) 2) :=
  ⟨fun a b => by rw [H2Pid.H_A1_two_eq_zero k l hl n hΛ a, H2Pid.H_A1_two_eq_zero k l hl n hΛ b]⟩

end RamanujanPetersson.EtCompact

end

end


