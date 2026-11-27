-- Prove2me | Definitions.Def_RPLib_FX_EtPBCC3_003
-- name    : RPLib_FX_EtPBCC3_003
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-27T06:29:45.957989+00:00
-- url     : https://prove2.me/theorems/1a049ee2-4c4d-4ffc-978c-10bff4451df0
-- title:
--   Compactly supported étale cohomology of affine space with Tate twists, library file 003
-- statement:
--   File 003 of the library for compactly supported étale cohomology of affine space with Tate twists: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_P1Hn`: S4-EtCompact: `H^2(G_m, Λ) = 0` and `H^(n+3)(P^1, Λ)` from the affine charts (O8c, file M7)
--
--   **Formalization note.** One file of a library formalizing the étale cohomology with compact supports of affine space over an algebraically closed field $K$ with Tate-twisted coefficients: for $\Lambda$ a finite ring with $\ell^m \Lambda = 0$ ($\ell$ invertible in $K$) and $\Lambda(k)$ the constant sheaf $(\Lambda \otimes \mu_{\ell^m})^{\otimes k}$, $H^q_c(\mathbb{A}^{n+1}_K, \Lambda(k)) = 0$ for $q \ne 2n+2$ and $H^{2n+2}_c(\mathbb{A}^{n+1}_K, \Lambda(n+1)) \cong \Lambda$ $\Lambda$-linearly, via $R^q \mathrm{pr}_!$ of the relative affine line and induction on the dimension. It builds on the proper base change libraries (`RPLib_FX_EtPBC_*`, `RPLib_FX_EtPBCB_*`, `RPLib_FX_EtPBCC1_*`, `RPLib_FX_EtPBCC2_*`). The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XVII (P. Deligne, cohomologie à supports propres) and Exposé XVIII, 2.9 (P. Deligne, morphisme trace), Lecture Notes in Math. 305, Springer (1973); P. Deligne, SGA 4 1/2, [Arcata], Lecture Notes in Math. 569 (1977); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_24

/-!
# Compactly supported étale cohomology of affine space with Tate twists, library file 003

Declarations of the formalization of compactly supported étale cohomology of affine space over an
algebraically closed field with Tate-twisted coefficients: H^q_c(A^(n+1), Λ(k)) = 0 for q ≠ 2n+2 and
H^(2n+2)_c(A^(n+1), Λ(n+1)) ≃ Λ, Λ-linearly, re-hosted declaration by declaration from the library
modules below, on top of the proper base change libraries RPLib_FX_EtPBC, RPLib_FX_EtPBCB,
RPLib_FX_EtPBCC1 and RPLib_FX_EtPBCC2. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_P1Hn`: S4-EtCompact: `H^2(G_m, Λ) = 0` and `H^(n+3)(P^1, Λ)` from the affine charts (O8c, file M7)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_P1Hn =====
section

/-!
# S4-EtCompact: `H^2(G_m, Λ) = 0` and `H^(n+3)(P^1, Λ)` from the affine charts (O8c, file M7)

* `LX.isC1_genField`, `LX.H_genPt_eq_zero`: the generic point of `G_m` is `C₁` (Tsen), so `H^(n+2)` vanishes there;
* **`Gm.H_two_eq_zero`**: `H^2(G_m, Λ) = 0` (`H2Pid.H_two_eq_zero_of_root` for the PID `k[X]_X`);
* `P1.hSuccEquiv`: `H^(n+1)(P^1, Λ) ≃+ H^n(G_m, Λ)` when `H^n(A^1, Λ) = H^(n+1)(A^1, Λ) = 0` (Mayer-Vietoris);
* **`P1.subsingleton_h_add_three`**: `H^(n+3)(P^1, Λ) = 0` when `H^(n+2)`, `H^(n+3)` of `A^1` and `H^(n+2)` of `G_m`
  vanish.
-/

set_option autoImplicit false

open Polynomial AlgebraicGeometry CategoryTheory

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves RamanujanPetersson.CdOne RamanujanPetersson.Tsen

section GmH2

end GmH2

section P1Hn

variable (K : Type) [Field K] {Λ : Type} [CommRing Λ]

set_option maxHeartbeats 1000000 in
/-- **`H^(n+1)(P^1, Λ) ≃ H^n(G_m, Λ)`** when `H^n(A^1, Λ) = H^(n+1)(A^1, Λ) = 0`. -/
def P1.hSuccEquiv (n : ℕ) (h1 : Subsingleton (H Λ (unitSh Λ (A1 K)) n))
    (h2 : Subsingleton (H Λ (unitSh Λ (A1 K)) (n + 1))) :
    H Λ (unitSh Λ (P1 K)) (n + 1) ≃ H Λ (unitSh Λ (Gm K)) n :=
  (Equiv.ofBijective _ (precomp_extClass_bijective (P1.seB K) (unitSh Λ (P1 K)) (Nat.add_comm 1 n)
    (P1.subB K n h1) (P1.subB K (n + 1) h2))).symm.trans (P1.h1InterB K n).toEquiv

end P1Hn

end RamanujanPetersson.EtCompact

end

end


