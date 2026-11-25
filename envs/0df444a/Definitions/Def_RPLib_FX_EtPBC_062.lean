-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_062
-- name    : RPLib_FX_EtPBC_062
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:28:25.980362+00:00
-- url     : https://prove2.me/theorems/f3117f34-9929-5ee9-8305-c406ef50f740
-- title:
--   Proper base change for the projective line, library file 062
-- statement:
--   File 062 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovPr12`: S4-EtPBC-A, R4-T2 (A3l): the kernel of reduction mod `J` on a presentation, and `resid_ker` with that target
--   * `S4.Def_RP_EtPBC_A_CovHat2`: S4-EtPBC-A, R4-T2 (A2c-3b): the completed overlap ring and the maps from the base charts
--   * `S4.Def_RP_EtPBC_A_LocFree`: S4-EtPBC-A, R4-T2 (A2c-5, E3b2): the primes over `J` lie in the free locus
--   * `S4.Def_RP_EtPBC_A_CovHat11`: S4-EtPBC-A, R4-T2 (A2c-3h): the level reductions of the completed overlap
--   * `S4.Def_RP_EtPBC_A_Z2H1`: S4-EtPBC-A, (Z2a-c): `H¹` over the two charts, Artin-Rees, lifting mod `I^n`
--   * `S4.Def_RP_EtPBC_A_Z4Glue`: S4-EtPBC-A, (Z) geometric layer 9 (G-e, part 1): gluing the two charts of `Y`
--   * `S4.Def_RP_EtPBC_A_CovY`: S4-EtPBC-A, R4-T2 (G1b): affine charts of `Y_{V'} = Y ×_V Spec R'`
--   * `S4.Def_RP_EtPBC_A_CovCv`: S4-EtPBC-A, R4-T2 (G1c, part 1): the locally directed chart cover of `Y_{V'}`
--   * `S4.Def_RP_EtPBC_A_CovFib`: S4-EtPBC-A, R4-T2 (G1d): the lifted cover restricts to the given fibre cover
--   * `S4.Def_RP_EtPBC_A_SecCoc`: S4-EtPBC-A, L1c (part 1): cocycles of `I^•(W)` as `Ext` classes
--   * `S4.Def_RP_EtPBC_A_VPart`: S4-EtPBC-A, M2 F7/F9a: the value function on points, and base change from a section with the same values
--   * `S4.Def_RP_EtPBC_A_DescG3`: S4-EtPBC-A, R4-T1c (part 2): the glued cover `U₀ ⟶ X` is finite, etale and surjective
--   * `S4.Def_RP_EtPBC_A_ESheet`: S4-EtPBC-A, M4(E), ESheet: the sheets of `W ×_P Y` and the sections `f_j`
--   * `S4.Def_RP_EtPBC_A_EG`: S4-EtPBC-A, M4(E), EG: relations of the sections `f_j` are relations of the generators near `ξ`
--   * `S4.Def_RP_EtPBC_A_CovNbB`: S4-EtPBC-A, R4-T2 (G2): the cover lifting property at a neighbourhood gives `LiftT`
--   * `S4.Def_RP_EtPBC_A_O2MV`: S4-EtPBC-A, O2 (MV route), MV: the Mayer-Vietoris sequence of free sheaves
--   * `S4.Def_RP_EtPBC_A_O2P1`: S4-EtPBC-A, O2 M5 P1: purity for Kummer roots on a Dedekind domain (field theory)
--   * `S4.Def_RP_EtPBC_A_O2PPTd`: S4-EtPBC-A, O2 GLOB (O2PPTd): the chart form of the piece transfer, and Zariski shrinks
--   * `S4.Def_RP_EtPBC_A_O2Gl2b`: S4-EtPBC-A, O2 GLOB (O2Gl2b): the charts of stage S3
--   * `S4.Def_RP_EtPBC_A_O2Gl2d`: S4-EtPBC-A, O2 GLOB (O2Gl2d): stage S4, the global unit `H` seen on `W₂`
--   * `S4.Def_RP_EtPBC_A_O2Gl2h`: S4-EtPBC-A, O2 GLOB (O2Gl2h): stage S4 on the charts, the data `e`, `g`, `hHp`, `hHq` of `uk_diff`
--   * `S4.Def_RP_EtPBC_A_O2LocU`: S4-EtPBC-A, O2 GLOB (O2LocU): changing the open of a one-point MV class
--   * `S4.Def_RP_EtPBC_A_O2PP4b`: S4-EtPBC-A, O2 PP' (O2PP4b): chart helpers for the S1 layer
--   * `S4.Def_RP_EtPBC_A_O2L1b`: S4-EtPBC-A, L1b (MVr): Mayer-Vietoris for free sheaves with arbitrary fibres of `Z`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_036
import Definitions.Def_RPLib_FX_EtPBC_050

/-!
# Proper base change for the projective line, library file 062

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovPr12`: S4-EtPBC-A, R4-T2 (A3l): the kernel of reduction mod `J` on a presentation, and `resid_ker` with that target
* `S4.Def_RP_EtPBC_A_CovHat2`: S4-EtPBC-A, R4-T2 (A2c-3b): the completed overlap ring and the maps from the base charts
* `S4.Def_RP_EtPBC_A_LocFree`: S4-EtPBC-A, R4-T2 (A2c-5, E3b2): the primes over `J` lie in the free locus
* `S4.Def_RP_EtPBC_A_CovHat11`: S4-EtPBC-A, R4-T2 (A2c-3h): the level reductions of the completed overlap
* `S4.Def_RP_EtPBC_A_Z2H1`: S4-EtPBC-A, (Z2a-c): `H¹` over the two charts, Artin-Rees, lifting mod `I^n`
* `S4.Def_RP_EtPBC_A_Z4Glue`: S4-EtPBC-A, (Z) geometric layer 9 (G-e, part 1): gluing the two charts of `Y`
* `S4.Def_RP_EtPBC_A_CovY`: S4-EtPBC-A, R4-T2 (G1b): affine charts of `Y_{V'} = Y ×_V Spec R'`
* `S4.Def_RP_EtPBC_A_CovCv`: S4-EtPBC-A, R4-T2 (G1c, part 1): the locally directed chart cover of `Y_{V'}`
* `S4.Def_RP_EtPBC_A_CovFib`: S4-EtPBC-A, R4-T2 (G1d): the lifted cover restricts to the given fibre cover
* `S4.Def_RP_EtPBC_A_SecCoc`: S4-EtPBC-A, L1c (part 1): cocycles of `I^•(W)` as `Ext` classes
* `S4.Def_RP_EtPBC_A_VPart`: S4-EtPBC-A, M2 F7/F9a: the value function on points, and base change from a section with the same values
* `S4.Def_RP_EtPBC_A_DescG3`: S4-EtPBC-A, R4-T1c (part 2): the glued cover `U₀ ⟶ X` is finite, etale and surjective
* `S4.Def_RP_EtPBC_A_ESheet`: S4-EtPBC-A, M4(E), ESheet: the sheets of `W ×_P Y` and the sections `f_j`
* `S4.Def_RP_EtPBC_A_EG`: S4-EtPBC-A, M4(E), EG: relations of the sections `f_j` are relations of the generators near `ξ`
* `S4.Def_RP_EtPBC_A_CovNbB`: S4-EtPBC-A, R4-T2 (G2): the cover lifting property at a neighbourhood gives `LiftT`
* `S4.Def_RP_EtPBC_A_O2MV`: S4-EtPBC-A, O2 (MV route), MV: the Mayer-Vietoris sequence of free sheaves
* `S4.Def_RP_EtPBC_A_O2P1`: S4-EtPBC-A, O2 M5 P1: purity for Kummer roots on a Dedekind domain (field theory)
* `S4.Def_RP_EtPBC_A_O2PPTd`: S4-EtPBC-A, O2 GLOB (O2PPTd): the chart form of the piece transfer, and Zariski shrinks
* `S4.Def_RP_EtPBC_A_O2Gl2b`: S4-EtPBC-A, O2 GLOB (O2Gl2b): the charts of stage S3
* `S4.Def_RP_EtPBC_A_O2Gl2d`: S4-EtPBC-A, O2 GLOB (O2Gl2d): stage S4, the global unit `H` seen on `W₂`
* `S4.Def_RP_EtPBC_A_O2Gl2h`: S4-EtPBC-A, O2 GLOB (O2Gl2h): stage S4 on the charts, the data `e`, `g`, `hHp`, `hHq` of `uk_diff`
* `S4.Def_RP_EtPBC_A_O2LocU`: S4-EtPBC-A, O2 GLOB (O2LocU): changing the open of a one-point MV class
* `S4.Def_RP_EtPBC_A_O2PP4b`: S4-EtPBC-A, O2 PP' (O2PP4b): chart helpers for the S1 layer
* `S4.Def_RP_EtPBC_A_O2L1b`: S4-EtPBC-A, L1b (MVr): Mayer-Vietoris for free sheaves with arbitrary fibres of `Z`
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_CovPr12 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3l): the kernel of reduction mod `J` on a presentation, and `resid_ker` with that target

* `presMap_mk_ker_le`: `ker (presMap (mk J) g) ≤ J · Pres g`.
* **`resid_ker_pm`**: `resid_ker` with `T := Pres (gmap (mk J) g')`, `q := presMap (mk J) g'` (s68 probe: the
  quotient `Pres g' ⧸ J · Pres` as `T` times out at `whnf`; this target elaborates in 26 s).
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Gen

end Gen

variable {Cc S S' : Type u} [CommRing Cc] [CommRing S] [CommRing S'] {r : ℕ} {Q : Type u} [CommRing Q]
variable (fh : Cc →+* S) (f' : Cc →+* S') (gC : Fin r → MvPolynomial (Fin r) Cc) (θh : Pres (gmap fh gC) →+* Q)
  (κ' : S' →+* Q) (hκ : κ'.comp f' = (θh.comp (algebraMap S (Pres (gmap fh gC)))).comp fh)

/-- `resid_ker` with the reduction `presMap (mk J)` as the comparison map. -/
theorem resid_ker_pm (hθ : Function.Surjective θh) (J : Ideal S') (hJ : ∀ a ∈ J, κ' a = 0)
    (lam : S →+* Pres (gmap (Ideal.Quotient.mk J) (gmap f' gC)))
    (hlam : ∀ c, lam (fh c) = presMap (Ideal.Quotient.mk J) (gmap f' gC) (algebraMap S' (Pres (gmap f' gC)) (f' c)))
    (I : Ideal S) (hI : RingHom.ker θh = I.map (algebraMap S (Pres (gmap fh gC)))) (hlamI : I ≤ RingHom.ker lam)
    (hsec : ∀ a : S', ∃ s : S, θh (algebraMap S (Pres (gmap fh gC)) s) = κ' a ∧
      lam s = presMap (Ideal.Quotient.mk J) (gmap f' gC) (algebraMap S' (Pres (gmap f' gC)) a)) :
    RingHom.ker (resid fh f' gC θh κ' hκ) = J.map (algebraMap S' (Pres (gmap f' gC))) :=
  resid_ker fh f' gC θh κ' hκ hθ J hJ _ (presMap_mk_ker_le J (gmap f' gC)) lam hlam I hI hlamI hsec

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovHat2 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-3b): the completed overlap ring and the maps from the base charts

* **`hE`** `⊆ L₀ × L₁` (fractions `x / T₁ᵃ T₀ᵇ`, `x ∈ Gam (a + b)`); **`hψ₀ : hE₀ →+* hE`**, **`hψ₁ : hE₁ →+* hE`**;
* `ρ₀_fB`, `ρ₁_fB`, **`famB_mem`**: `(fB₀ b₀, fB₁ b₁) ∈ Gam d` when `φ₀ b₀ = φ₀ t₀ ^ d * φ₁ b₁`;
* **`liftN₀ : N →+* L₀`**, **`liftN₁ : N →+* L₁`** (from `N = B₀[1/t₀] = B₁[1/t₁]`), `liftN₀_φ₀`, `liftN₁_φ₁`,
  `liftN₀_inv`, `liftN₁_inv`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Hat2

variable {B₀ B₁ N : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k))

theorem liftN₀_inv (hts : φ₀ t₀ * φ₁ t₁ = 1) (hφ₀ : IsAwayMap φ₀ t₀) (hu₀ : IsUnit (φ₀ t₀)) :
    jL₀ C (tFm C) * liftN₀ C hφ₀ hu₀ (φ₁ t₁) = 1 := by
  rw [← liftN₀_φ₀ C hφ₀ hu₀ t₀, ← map_mul, hts, map_one]

end Hat2

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_LocFree =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-5, E3b2): the primes over `J` lie in the free locus

For a noetherian ring `A`, an ideal `J` and a finite `A`-module `M` with `M ⧸ J^(k+1) M` flat over `A ⧸ J^(k+1)` for
all `k`:
* `lf_flat_quot_iff`: flatness of `M ⧸ I M` over `A ⧸ I` is flatness of `(A ⧸ I) ⊗ M`;
* `lf_flat_loc`: it passes to any `A`-algebra `Rₚ` (`Rₚ ⊗ M` modulo `I Rₚ`);
* **`lf_mem_freeLocus`**: every prime `𝔮 ⊇ J` lies in `Module.freeLocus A M`.
-/

set_option autoImplicit false

noncomputable section

open TensorProduct IsLocalRing

namespace RamanujanPetersson.EtPBC.Cov

universe u

section LocFree

/-- **Free at the primes over `J`** (local flatness criterion, global form). -/
theorem lf_mem_freeLocus {A M : Type u} [CommRing A] [IsNoetherianRing A] [AddCommGroup M] [Module A M]
    [Module.Finite A M] (J : Ideal A)
    (hfl : ∀ k : ℕ, Module.Flat (A ⧸ J ^ (k + 1)) (M ⧸ (J ^ (k + 1) • ⊤ : Submodule A M)))
    (q : PrimeSpectrum A) (hq : J ≤ q.asIdeal) : q ∈ Module.freeLocus A M := by
  rw [Module.mem_freeLocus_iff_tensor q (Localization.AtPrime q.asIdeal)]
  have hJ1 : J.map (algebraMap A (Localization.AtPrime q.asIdeal)) ≤
      maximalIdeal (Localization.AtPrime q.asIdeal) :=
    (Ideal.map_mono hq).trans (Localization.AtPrime.map_eq_maximalIdeal).le
  have hJ' : J.map (algebraMap A (Localization.AtPrime q.asIdeal)) ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (h.symm.trans_le hJ1))
  refine free_of_quot_flat' (fun k => (J ^ (k + 1)).map (algebraMap A (Localization.AtPrime q.asIdeal)))
    (fun k h => hJ' ?_) (fun a ha => ?_) (fun k => lf_flat_loc _ _ (hfl k))
  · rw [eq_top_iff, ← h]
    show (J ^ (k + 1)).map (algebraMap A (Localization.AtPrime q.asIdeal)) ≤ _
    rw [Ideal.map_pow]
    exact Ideal.pow_le_self (Nat.succ_ne_zero k)
  · have h : a ∈ ⨅ i : ℕ, (J.map (algebraMap A (Localization.AtPrime q.asIdeal))) ^ i :=
      (Submodule.mem_iInf _).mpr fun i => Ideal.pow_le_pow_right (Nat.le_succ i)
        (by rw [← Ideal.map_pow]; exact ha i)
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ hJ'] at h
    exact (Submodule.mem_bot _).mp h

end LocFree

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovHat11 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-3h): the level reductions of the completed overlap

* `ev₀ k : L₀ → E(k)` (the lift of `ψ₀ ∘ eval k`, `t ↦ u` is a unit), `ev₀_jL₀`;
* **`θ k : Ê → E(k)`**, compatible with the chart reductions: **`θ_hψ₀`** (`θ ∘ ψ̂₀ = ψ₀ ∘ θ₀`), **`θ_hψ₁`**
  (`θ ∘ ψ̂₁ = ψ₁ ∘ θ₁`), and with the structure maps: **`θ_β`** (`θ ∘ β = a ∘ mk`).
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Ov

variable {B₀ B₁ N : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k)) (hts : φ₀ t₀ * φ₁ t₁ = 1)
  (hφ₀ : IsAwayMap φ₀ t₀) (hu₀ : IsUnit (φ₀ t₀)) (hφ₁ : IsAwayMap φ₁ t₁) (hu₁ : IsUnit (φ₁ t₁))

theorem ev₀_jL₀ (k : ℕ) (y : ∀ k, (C k).E₀) : ev₀ C hts k (jL₀ C y) = (C k).ψ₀ (y k) :=
  IsLocalization.Away.lift_eq _ _ _

end Ov

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_Z2H1 =====
section

/-!
# S4-EtPBC-A, (Z2a-c): `H¹` over the two charts, Artin-Rees, lifting mod `I^n`

Two-chart data as in `Z1.twoChart_fg`: `φ₀ : M₀ →ₗ[A[X]] N`, `φ₁ : M₁ →ₗ[A] N` with `X • φ₁ (X • m) = φ₁ m`.
`W := φ₀(M₀) + φ₁(M₁)` (`chartIm`), so that `H¹ = N / W`.

* **`h1_span`**: if `M₁` is finite over `A[X]`, every `y ∈ N` is `X^k • φ₁ b` and every `φ₁ m` is moved into the
  image of `φ₀` by a power of `X`, then `N = U + W` with `U` finite over `A` (`H¹` is finite over `A`).
* **`artinRees_sup`**: `N = U + W` with `U` finite, `A` noetherian: `∃ c, ∀ n, I^(n+c) N ∩ W ≤ I^n W`.
* **`lift_twoChart`**: `∃ c, ∀ n a b, φ₀ a - φ₁ b ∈ I^(n+c) N → ∃ a' b', φ₀ a' = φ₁ b'` with `a' ≡ a`, `b' ≡ b`
  mod `I^n`.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Z2

open RamanujanPetersson.EtPBC.Z1

universe u v w w'

variable {A : Type u} [CommRing A]

section Span

end Span

section ArtinRees

end ArtinRees

section Lift

variable {M₀ : Type v} {M₁ : Type w} {N : Type w'}
  [AddCommGroup M₀] [Module A[X] M₀] [Module A M₀] [IsScalarTower A A[X] M₀]
  [AddCommGroup M₁] [Module A[X] M₁] [Module A M₁] [IsScalarTower A A[X] M₁]
  [AddCommGroup N] [Module A[X] N] [Module A N] [IsScalarTower A A[X] N]

/-- **Lifting mod `I^n`**: a pair agreeing on the overlap mod `I^(n+c)` is congruent mod `I^n` to a section. -/
theorem lift_twoChart [IsNoetherianRing A] [Module.Finite A[X] M₁] (I : Ideal A) (φ₀ : M₀ →ₗ[A[X]] N)
    (φ₁ : M₁ →ₗ[A] N) (h₁ : ∀ m, (X : A[X]) • φ₁ ((X : A[X]) • m) = φ₁ m)
    (hgen : ∀ m : M₁, ∃ (d : ℕ) (a : M₀), φ₀ a = (X ^ d : A[X]) • φ₁ m)
    (hloc : ∀ y : N, ∃ (k : ℕ) (b : M₁), y = (X ^ k : A[X]) • φ₁ b) :
    ∃ c : ℕ, ∀ (n : ℕ) (a : M₀) (b : M₁), φ₀ a - φ₁ b ∈ (I ^ (n + c) • ⊤ : Submodule A N) →
      ∃ (a' : M₀) (b' : M₁), φ₀ a' = φ₁ b' ∧ a - a' ∈ (I ^ n • ⊤ : Submodule A M₀) ∧
        b - b' ∈ (I ^ n • ⊤ : Submodule A M₁) := by
  obtain ⟨U, hU, hUW⟩ := h1_span φ₀ φ₁ h₁ hgen hloc
  obtain ⟨c, hc⟩ := artinRees_sup I U (chartIm φ₀ φ₁) hU hUW
  refine ⟨c, fun n a b hab => ?_⟩
  have hW : φ₀ a - φ₁ b ∈ chartIm φ₀ φ₁ :=
    Submodule.sub_mem _ (mem_chartIm₀ φ₀ φ₁ a) (mem_chartIm₁ φ₀ φ₁ b)
  obtain ⟨a'', b'', ha'', hb'', he⟩ := mem_smul_chartIm (I ^ n) φ₀ φ₁ (hc n ⟨hab, hW⟩)
  refine ⟨a - a'', b + b'', ?_, by rw [sub_sub_cancel]; exact ha'',
    by rw [sub_add_cancel_left]; exact Submodule.neg_mem _ hb''⟩
  rw [map_sub, map_add, sub_eq_iff_eq_add.1 he]
  abel

end Lift
end RamanujanPetersson.EtPBC.Z2
end

end

-- ===== S4.Def_RP_EtPBC_A_Z4Glue =====
section

/-!
# S4-EtPBC-A, (Z) geometric layer 9 (G-e, part 1): gluing the two charts of `Y`

* `chU_sup`: `D₊(X₀) ⊔ D₊(X₁) = ⊤`; `Yc_sup`: `Y₀ ⊔ Y₁ = ⊤`.
* `struct_res`: the structure map `Γ(V) → Γ(Y, ⊤)` restricts to the chart structures; `map_map`.
* **`glueRing : secAlg φY0 φY1 →+* Γ(Y, ⊤)`** (sheaf gluing), `glueRing_res0`, `glueRing_res1`, `eq_of_res`,
  `glueRing_struct`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace HomogeneousLocalization
open RamanujanPetersson.EtCompact
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtPBC.Z3

universe u

variable (K : Type u) [Field K]

variable {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}} (π : Y ⟶ PV K gV)

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN

/-- **The glued section is compatible with the structure maps.** -/
theorem glueRing_struct (a : Γ(V, ⊤)) :
    glueRing K gV π (algebraMap Γ(V, ⊤) (Z2.secAlg (φY0 K gV π) (φY1 K gV π)) a) = (π ≫ qV K gV).appTop a := by
  apply eq_of_res K gV π
  · rw [glueRing_res0]
    exact congrArg (fun φ => φ.hom a) (struct_res K gV π 0)
  · rw [glueRing_res1]
    exact congrArg (fun φ => φ.hom a) (struct_res K gV π 1)

end RamanujanPetersson.EtPBC.Z3

end

end

-- ===== S4.Def_RP_EtPBC_A_CovY =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1b): affine charts of `Y_{V'} = Y ×_V Spec R'`

For an affine open `U ⊆ Y` (with `Γ(V) → Γ(Y, U)` the structure map), **`chY hU hA`** `: Spec (R' ⊗ Γ(Y, U)) ⟶ Y_{V'}`
is the base change of `hU.fromSpec` along `Y_{V'} ⟶ Y` (**`isPullback_chY`**), an open immersion with range
`fst⁻¹ U` (**`opensRange_chY`**), compatible with restrictions (**`chY_res`**).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open RamanujanPetersson.EtPBC.Z3

universe u

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV) [IsAffine V] (R' : Type u) [CommRing R'] [Algebra Γ(V, ⊤) R']

section Chart

variable {U : Y.Opens} (hU : IsAffineOpen U) [Algebra Γ(V, ⊤) Γ(Y, U)]
  (hA : CommRingCat.ofHom (algebraMap Γ(V, ⊤) Γ(Y, U)) = strU K gV π U)

@[reassoc (attr := simp)]
theorem chY_fst : chY K gV π R' hU hA ≫ pullback.fst (π ≫ qV K gV) (hV V R') =
    Spec.map (CommRingCat.ofHom (S := R' ⊗[Γ(V, ⊤)] Γ(Y, U)) Algebra.TensorProduct.includeRight.toRingHom) ≫
      hU.fromSpec :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem chY_snd : chY K gV π R' hU hA ≫ pullback.snd (π ≫ qV K gV) (hV V R') =
    Spec.map (CommRingCat.ofHom (S := R' ⊗[Γ(V, ⊤)] Γ(Y, U)) Algebra.TensorProduct.includeLeftRingHom) :=
  pullback.lift_snd _ _ _

end Chart

section Res

end Res

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovCv =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1c, part 1): the locally directed chart cover of `Y_{V'}`

`directed_of_range`: directedness of an open cover from its ranges. **`covV`**: the open cover of `Y_{V'} = Y ×_V Spec R'`
by the charts `Spec (R' ⊗ Γ(Y₀₁))`, `Spec (R' ⊗ Γ(Y₀))`, `Spec (R' ⊗ Γ(Y₁))`, indexed by `WalkingSpan`
(`zero ↦ Y₀₁`), with transition maps the `span` of the chart restrictions `a0`, `a1`; instance `LocallyDirected`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open RamanujanPetersson.EtPBC.Z3

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN

universe u

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV) [IsAffine V] [IsAffineHom π] (R' : Type u) [CommRing R'] [Algebra Γ(V, ⊤) R']

/-- The chart over `Y₀`. -/
abbrev ch0 : Spec (CommRingCat.of (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0))) ⟶ YV K gV π R' :=
  chY K gV π R' (isAffineOpen_Yc K gV π 0) (struct_res K gV π 0)

/-- The chart over `Y₁`. -/
abbrev ch1 : Spec (CommRingCat.of (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 1))) ⟶ YV K gV π R' :=
  chY K gV π R' (isAffineOpen_Yc K gV π 1) (struct_res K gV π 1)

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovFib =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1d): the lifted cover restricts to the given fibre cover

For lift data `L : LiftD K gV π x q hx` of a fibre cover `q : T ⟶ Y_x`: the glued cover `dL L` of `Y_{V'}`
(`V' = Spec L.R'`), the lift `xL L` of `x`, and **`ψL L : U_x ⟶ T`** on `U_x = (dL L).glued ×_{Y_{V'}} Y_x`, glued
from the chart lifts `gW` (`g0`, `g1`; `overlap` on `Y₀₁`), with **`ψL_q`**: `ψL L ≫ q = pullback.snd`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open RamanujanPetersson.EtPBC.Z3

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN algKY algT CoverLift.cR CoverLift.aR CoverLift.c₀ CoverLift.c₁ CoverLift.c₀₁ CoverLift.a₀ CoverLift.a₁ CoverLift.a₀₁

universe u

variable {K : Type u} [Field K] {V : Scheme.{u}} {gV : V ⟶ Spec (CommRingCat.of K)} {Y : Scheme.{u}}
  {π : Y ⟶ PV K gV} {x : Spec (CommRingCat.of K) ⟶ V} [IsAffine V] [IsFinite π] {hx : x ≫ gV = 𝟙 _}
  {T : Scheme.{u}} {q : T ⟶ Yx K gV π x} [IsAffineHom q] (L : LiftD K gV π x q hx)

/-- The lift `Spec K ⟶ Spec R'` of `x`. -/
abbrev xL : letI := algKV K gV; Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of L.R') :=
  letI := algKV K gV; Spec.map (CommRingCat.ofHom L.χ')

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_SecCoc =====
section

/-!
# S4-EtPBC-A, L1c (part 1): cocycles of `I^•(W)` as `Ext` classes

For an injective resolution `I` of `F`, `W : X.Etale` and `p : ℕ`: `secSc Λ I W p` is the short complex `sc (p+1)` of
the complex of sections `I^•(W)`; `cocExtFun` sends a cocycle `z` (an element of `ker g`) to the class
`InjectiveResolution.extMk` of the map `Λ[W] ⟶ I^(p+1)` given by `z` (`freeEquiv`); it is additive (`cocExtFun_add`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}} {F : EtSh Λ X} (I : InjectiveResolution F)

/-- A cocycle of `I^•(W)` in degree `p+1` as a class in `Ext^(p+1)(Λ[W], F)`. -/
def cocExtFun (W : X.Etale) (p : ℕ) (z : LinearMap.ker (secSc Λ I W p).g.hom) : Ext.{u} (freeSh Λ W) F (p + 1) :=
  I.extMk ((freeEquiv Λ W (I.cocomplex.X (p + 1))).symm (cocSec Λ I z))
    ((ComplexShape.up ℕ).next (p + 1)) (up_next p) (cocExt_aux Λ I W p z)

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_VPart =====
section

/-!
# S4-EtPBC-A, M2 F7/F9a: the value function on points, and base change from a section with the same values

* `vval_locConst₂`: `vval_locConst` with test points over any separably closed field;
* `vv b q := vval b (geomPtAt q).pt`, **`vval_eq_vv`** (`vval b τ = vv b (τ pt)`), **`isLocallyConstant_vv`**;
* `fibInc σ : fib π (σ ≫ ι) ⟶ Y ×_P X` and **`psi_xi_eq_vval`**: `Ψ(ξ_σ b)(x) = vval b (x̄ ≫ fibInc σ)`;
* `ysj j : Y ×_P P_s ⟶ Y ×_P P_V` and **`vval_bc`**: the value of a base-changed class is `cval z ∘ ysj j`;
* **`bc_eq_of_vv`**: a section `z` over `Y ×_P P_V` with `cval z ∘ ysj j = vv b` gives `bc z = b`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite GrothendieckTopology

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtCompact.Supp

universe u

section Gen

variable {Λ : Type u} [CommRing Λ] {X P Y : Scheme.{u}} (ι : X ⟶ P) (π : Y ⟶ P) {M : ModuleCat.{u} Λ}

/-- **`vval b` is locally constant**, tested over all separably closed fields. -/
theorem vval_locConst₂ {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (b : unitSh Λ X ⟶ (pull ι Λ).obj ((push π Λ).obj (constSh Λ Y M)))
    (τ : Spec (CommRingCat.of Ω) ⟶ pullback π ι) :
    ∃ N : Set ↑(pullback π ι), IsOpen N ∧ τ (default : Spec (CommRingCat.of Ω)) ∈ N ∧
      ∀ (Ω' : Type u) [Field Ω'] [IsSepClosed Ω'] (τ' : Spec (CommRingCat.of Ω') ⟶ pullback π ι),
        τ' (default : Spec (CommRingCat.of Ω')) ∈ N → vval ι π b τ' = vval ι π b τ := by
  obtain ⟨W, U, h, u, z, hb⟩ := exists_pullRep ι π (sigPt ι π τ) b
  have hu : τ ≫ pullback.snd π ι = u.left ≫ U.hom := (Over.w u).symm
  let l₀ : Spec (CommRingCat.of Ω) ⟶ pullback (pullback.snd π ι) U.hom := pullback.lift τ u.left hu
  have hl₀ : l₀ ≫ pullback.fst _ _ = τ := pullback.lift_fst _ _ _
  have hv₀ := vval_of_lift ι π b h z hb τ l₀ hl₀
  have hc : IsLocallyConstant (fun z' : ↑(pullback (pullback.snd π ι) U.hom) => cval z (kap ι π h z')) :=
    (isLocallyConstant_cval z).comp_continuous (kap ι π h).continuous
  have hN' := hc.isOpen_fiber (cval z (kap ι π h (l₀ (default : Spec (CommRingCat.of Ω)))))
  have : Etale U.hom := U.prop
  refine ⟨(pullback.fst (pullback.snd π ι) U.hom) '' ((fun z' => cval z (kap ι π h z')) ⁻¹'
    {cval z (kap ι π h (l₀ (default : Spec (CommRingCat.of Ω))))}),
    (pullback.fst (pullback.snd π ι) U.hom).isOpenMap _ hN', ⟨l₀ (default : Spec (CommRingCat.of Ω)), rfl,
      congrArg (fun φ => φ.base (default : Spec (CommRingCat.of Ω))) hl₀⟩, ?_⟩
  rintro Ω' _ _ τ' ⟨z', hz', hz'τ⟩
  obtain ⟨l', hl', hl'pt⟩ :=
    Scheme.exists_fac_of_etale_of_isSepClosed (Ω := Ω') (pullback.fst (pullback.snd π ι) U.hom) τ' z' hz'τ
  refine (vval_of_lift ι π b h z hb τ' l' hl').trans (Eq.trans ?_ hv₀.symm)
  rw [hl'pt]
  exact hz'

theorem vval_eq_vv (b : unitSh Λ X ⟶ (pull ι Λ).obj ((push π Λ).obj (constSh Λ Y M)))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (τ : Spec (CommRingCat.of Ω) ⟶ pullback π ι) :
    vval ι π b τ = vv ι π b (τ (default : Spec (CommRingCat.of Ω))) := by
  obtain ⟨N, -, hN, hc⟩ := vval_locConst₂ ι π b (geomPtAt (τ (default : Spec (CommRingCat.of Ω)))).pt
  have hq : (geomPtAt (τ (default : Spec (CommRingCat.of Ω)))).pt
      (default : Spec (CommRingCat.of (geomPtAt (τ (default : Spec (CommRingCat.of Ω)))).Ω)) =
      τ (default : Spec (CommRingCat.of Ω)) := center_geomPtAt _
  exact hc Ω τ (hq ▸ hN)

/-- **`Ψ(ξ_σ b)` at any point of the fibre is a value of `vval b`.** -/
theorem psi_xi_eq_vval (b : unitSh Λ X ⟶ (pull ι Λ).obj ((push π Λ).obj (constSh Λ Y M)))
    (σ : GeomPt X) (x : fib π (σ.map ι)) :
    psi π (σ.map ι) (xi ι σ ((push π Λ).obj (constSh Λ Y M)) b) x =
      vval ι π b ((geomPtAt x).pt ≫ fibInc ι π σ) := by
  obtain ⟨W, U, h, u, z, hb⟩ := exists_pullRep ι π σ b
  have e1 := xi_of_pullRep ι π b h z hb σ u
  have hu : (σ.liftOf u).left ≫ U.hom = σ.pt := Over.w (σ.liftOf u)
  have g1 : fibInc ι π σ ≫ pullback.fst π ι = pullback.fst π (σ.map ι).pt := pullback.lift_fst _ _ _
  have g2 : fibInc ι π σ ≫ pullback.snd π ι = pullback.snd π (σ.map ι).pt ≫ σ.pt := pullback.lift_snd _ _ _
  have hl : ((geomPtAt x).pt ≫ fibInc ι π σ) ≫ pullback.snd π ι =
      ((geomPtAt x).pt ≫ pullback.snd π (σ.map ι).pt ≫ (σ.liftOf u).left) ≫ U.hom :=
    (Category.assoc _ _ _).trans ((congrArg ((geomPtAt x).pt ≫ ·) g2).trans
      (((congrArg (fun m => (geomPtAt x).pt ≫ pullback.snd π (σ.map ι).pt ≫ m) hu.symm).trans
        (congrArg ((geomPtAt x).pt ≫ ·)
          (Category.assoc (pullback.snd π (σ.map ι).pt) (σ.liftOf u).left U.hom).symm)).trans
        (Category.assoc (geomPtAt x).pt (pullback.snd π (σ.map ι).pt ≫ (σ.liftOf u).left) U.hom).symm))
  let l : Spec (CommRingCat.of (geomPtAt x).Ω) ⟶ pullback (pullback.snd π ι) U.hom := pullback.lift _ _ hl
  have hl₁ : l ≫ pullback.fst _ _ = (geomPtAt x).pt ≫ fibInc ι π σ := pullback.lift_fst _ _ _
  have hl₂ : l ≫ pullback.snd (pullback.snd π ι) U.hom =
      (geomPtAt x).pt ≫ pullback.snd π (σ.map ι).pt ≫ (σ.liftOf u).left := pullback.lift_snd _ _ _
  have e2 := vval_of_lift ι π b h z hb _ l hl₁
  have e3 : (geomPtAt x).pt ≫ fibToNbhd π (σ.map ι)
      ⟨W, (fiberMapIso ι σ).inv.app W (σ.point.fiber.map h u)⟩ = l ≫ kap ι π h := by
    apply pullback.hom_ext
    · have f1 := fibToNbhd_fst π (σ.map ι) ⟨W, (fiberMapIso ι σ).inv.app W (σ.point.fiber.map h u)⟩
      have f2 : ((fiberMapIso ι σ).inv.app W (σ.point.fiber.map h u)).left =
          ((σ.liftOf u).left ≫ h.left) ≫ pullback.fst W.hom ι :=
        (left_fiberMapIso_inv ι σ W (σ.point.fiber.map h u)).trans
          (congrArg (· ≫ pullback.fst W.hom ι) (liftOf_map_left' σ h u))
      have f3 : kap ι π h ≫ pullback.fst W.hom π =
          pullback.snd (pullback.snd π ι) U.hom ≫ h.left ≫ pullback.fst W.hom ι := pullback.lift_fst _ _ _
      refine (Category.assoc _ _ _).trans ((congrArg ((geomPtAt x).pt ≫ ·) f1).trans ?_)
      refine (congrArg (fun m => (geomPtAt x).pt ≫ pullback.snd π (σ.map ι).pt ≫ m) f2).trans ?_
      refine (congrArg (fun m => (geomPtAt x).pt ≫ pullback.snd π (σ.map ι).pt ≫ m)
        (Category.assoc (σ.liftOf u).left h.left (pullback.fst W.hom ι))).trans ?_
      refine (congrArg ((geomPtAt x).pt ≫ ·) (Category.assoc (pullback.snd π (σ.map ι).pt) (σ.liftOf u).left
        (h.left ≫ pullback.fst W.hom ι)).symm).trans ?_
      refine (Category.assoc (geomPtAt x).pt (pullback.snd π (σ.map ι).pt ≫ (σ.liftOf u).left)
        (h.left ≫ pullback.fst W.hom ι)).symm.trans ?_
      refine (congrArg (· ≫ h.left ≫ pullback.fst W.hom ι) hl₂.symm).trans ?_
      exact (Category.assoc _ _ _).trans ((congrArg (l ≫ ·) f3.symm).trans (Category.assoc _ _ _).symm)
    · have f4 : kap ι π h ≫ pullback.snd W.hom π =
          pullback.fst (pullback.snd π ι) U.hom ≫ pullback.fst π ι := pullback.lift_snd _ _ _
      refine (Category.assoc _ _ _).trans ((congrArg ((geomPtAt x).pt ≫ ·) (fibToNbhd_snd π _ _)).trans ?_)
      refine Eq.trans ?_ ((Category.assoc l (kap ι π h) (pullback.snd W.hom π)).trans (congrArg (l ≫ ·) f4)).symm
      refine Eq.trans ?_ (Category.assoc l (pullback.fst (pullback.snd π ι) U.hom) (pullback.fst π ι))
      refine Eq.trans ?_ (congrArg (· ≫ pullback.fst π ι) hl₁.symm)
      exact (congrArg ((geomPtAt x).pt ≫ ·) g1.symm).trans
        (Category.assoc (geomPtAt x).pt (fibInc ι π σ) (pullback.fst π ι)).symm
  have hpt := congrArg (fun φ => φ.base (default : Spec (CommRingCat.of (geomPtAt x).Ω))) e3
  have hx : (geomPtAt x).pt (default : Spec (CommRingCat.of (geomPtAt x).Ω)) = x := center_geomPtAt x
  refine (congrArg (fun e => psi π (σ.map ι) e x) e1).trans ((psi_germ π (σ.map ι)
    ⟨W, (fiberMapIso ι σ).inv.app W (σ.point.fiber.map h u)⟩ z x).trans ?_)
  refine Eq.trans ?_ e2.symm
  exact (congrArg (fun w => cval z (fibToNbhd π (σ.map ι)
    ⟨W, (fiberMapIso ι σ).inv.app W (σ.point.fiber.map h u)⟩ w)) hx.symm).trans (congrArg (cval z) hpt)

end Gen

section BC

variable {Λ : Type u} [CommRing Λ] {P S Y : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S) (π : Y ⟶ P)
  {M : ModuleCat.{u} Λ}

/-- **The value of a base-changed class.** -/
theorem vval_bc (j : Nbhd s) (φ : (nbhdSys Λ g s).obj j ⟶ (push π Λ).obj (constSh Λ Y M))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (τ : Spec (CommRingCat.of Ω) ⟶ pullback π (fibι g s)) :
    vval (fibι g s) π (bcUnit Λ g s j ≫ (pull (fibι g s) Λ).map φ) τ =
      cval (T := (etPull π).obj ((etPull g).obj j.1))
        (freeEquiv Λ ((etPull g).obj j.1) ((push π Λ).obj (constSh Λ Y M)) φ)
        (ysj g s π j (τ (default : Spec (CommRingCat.of Ω)))) := by
  have hl : τ ≫ pullback.snd π (fibι g s) = (τ ≫ pullback.snd π (fibι g s)) ≫ (etId (fib g s)).hom :=
    (Category.comp_id _).symm
  let l : Spec (CommRingCat.of Ω) ⟶ pullback (pullback.snd π (fibι g s)) (etId (fib g s)).hom :=
    pullback.lift τ _ hl
  have hl₁ : l ≫ pullback.fst _ _ = τ := pullback.lift_fst _ _ _
  have hl₂ : l ≫ pullback.snd _ _ = τ ≫ pullback.snd π (fibι g s) := pullback.lift_snd _ _ _
  have e1 := vval_of_lift (fibι g s) π (bcUnit Λ g s j ≫ (pull (fibι g s) Λ).map φ) (nbhdSec g s j)
    (freeEquiv Λ ((etPull g).obj j.1) ((push π Λ).obj (constSh Λ Y M)) φ)
    (sc_bcUnit_comp Λ g s j ((push π Λ).obj (constSh Λ Y M)) φ) τ l hl₁
  have y1 : ysj g s π j ≫ pullback.fst (pullback.snd j.1.hom g) π =
      pullback.snd π (fibι g s) ≫ fibToNbhd g s j := pullback.lift_fst _ _ _
  have y2 : ysj g s π j ≫ pullback.snd (pullback.snd j.1.hom g) π = pullback.fst π (fibι g s) :=
    pullback.lift_snd _ _ _
  have e2 : l ≫ kap (fibι g s) π (nbhdSec g s j) = τ ≫ ysj g s π j := by
    apply pullback.hom_ext
    · have f3 : kap (fibι g s) π (nbhdSec g s j) ≫ pullback.fst (pullback.snd j.1.hom g) π =
          pullback.snd (pullback.snd π (fibι g s)) (etId (fib g s)).hom ≫ secL g s j ≫
            pullback.fst (pullback.snd j.1.hom g) (fibι g s) := pullback.lift_fst _ _ _
      refine (Category.assoc _ _ _).trans ((congrArg (l ≫ ·) f3).trans ?_)
      refine (congrArg (fun m => l ≫ pullback.snd (pullback.snd π (fibι g s)) (etId (fib g s)).hom ≫ m)
        (secL_fst g s j)).trans ?_
      refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ fibToNbhd g s j) hl₂).trans ?_)
      exact (Category.assoc τ (pullback.snd π (fibι g s)) (fibToNbhd g s j)).trans
        ((congrArg (τ ≫ ·) y1.symm).trans (Category.assoc τ (ysj g s π j) _).symm)
    · have f4 : kap (fibι g s) π (nbhdSec g s j) ≫ pullback.snd (pullback.snd j.1.hom g) π =
          pullback.fst (pullback.snd π (fibι g s)) (etId (fib g s)).hom ≫ pullback.fst π (fibι g s) :=
        pullback.lift_snd _ _ _
      refine (Category.assoc _ _ _).trans ((congrArg (l ≫ ·) f4).trans ?_)
      refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst π (fibι g s)) hl₁).trans ?_)
      exact (congrArg (τ ≫ ·) y2.symm).trans (Category.assoc τ (ysj g s π j) _).symm
  have hpt := congrArg (fun φ => φ.base (default : Spec (CommRingCat.of Ω))) e2
  exact e1.trans (congrArg (cval (T := (etPull π).obj ((etPull g).obj j.1))
    (freeEquiv Λ ((etPull g).obj j.1) ((push π Λ).obj (constSh Λ Y M)) φ)) hpt)

end BC

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_DescG3 =====
section

/-!
# S4-EtPBC-A, R4-T1c (part 2): the glued cover `U₀ ⟶ X` is finite, etale and surjective

* Generic (any coequifibered `α : 𝒪_X ⟶ F` on affine opens): `glD H` (the relative gluing data),
  `cover_toBase` (`Spec F(U) ⟶ U₀ ⟶ X` is `Spec α_U ≫ U.fromSpec`), `prop_toBase` (a Zariski-local property holds
  for `toBase` once it holds for every `Spec α_U`), `isFinite_toBase`, `etale_toBase`, `surjective_toBase`.
* For `V` etale and surjective over `X` with `V.hom` affine: `surj_comap`, the instance
  `Module.FaithfullyFlat Γ(X, U) (CU V U)`, and for the descended presheaf `FU`:
  **`U0`**, **`toU0`** `: U0 ⟶ X` with `IsFinite`, `Etale`, `Surjective`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.DescG

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.DescA TensorProduct

universe u

section Base

end Base

section Cover

variable {X : Scheme.{u}} (V : X.Etale) [IsAffineHom V.hom]

variable [Surjective V.hom] {Λ : Type u} [CommRing Λ] {M : ModuleCat.{u} Λ} [Fintype M] [DecidableEq M]
  {E Q : EtSh Λ X} (a : constSh Λ X M ⟶ E) (b : E ⟶ Q) (hab : a ≫ b = 0)
  (hS : (ShortComplex.mk a b hab).ShortExact) (e : E.obj.obj (op V))
  (he : ∀ (W : X.Etale) (w₁ w₂ : W ⟶ V), (b.hom.app (op W)).hom ((E.obj.map w₁.op).hom e) =
    (b.hom.app (op W)).hom ((E.obj.map w₂.op).hom e))

theorem surj_B (U : X.AffineZariskiSite) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap Γ(X, U.1) (datA V a b hab hS e he U).B)) := by
  intro p
  obtain ⟨Q, hQ, hQp⟩ := (datA V a b hab hS e he U).exists_prime_over p.asIdeal
  exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQp⟩

end Cover

end RamanujanPetersson.EtPBC.DescG

end

end

-- ===== S4.Def_RP_EtPBC_A_ESheet =====
section

/-!
# S4-EtPBC-A, M4(E), ESheet: the sheets of `W ×_P Y` and the sections `f_j`

* `Nn ξ W` the relative normalization of `W` in `X' = Spec κ(ξ) ×_P W`; `Up ξ W := W ×_P Y`;
  `κp : X' ⟶ Up`, `ψn : Up ⟶ Nn` (inverse of `normalizationPullback`, `W` etale), `κp_ψn : κp ≫ ψn = toNormalization`;
* **`exists_sheets`**: a clopen partition `C b` of `Up` indexed by the fibre points `b` of `W` over `x̄`, with
  `κp (sx (τ b) pt) ∈ C b`;
* **`exists_fsec`**: a section of the constant sheaf with value `n i` on the `i`-th set of a finite clopen partition.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.GenGeo

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech

universe u

variable {P : Scheme.{u}} {T : P.Etale} (ξ : T.left) (W : P.Etale)

/-- **The sheets**: a clopen partition of `W ×_P Y` indexed by the points of `W` over `x̄`. -/
theorem exists_sheets [IsAffine W.left] (x : P) (t : (geomPtAt x).point.fiber.obj T)
    (τ : (geomPtAt x).point.fiber.obj W → (T ⟶ W)) (hτ : ∀ b, (geomPtAt x).point.fiber.map (τ b) t = b)
    [Finite ((geomPtAt x).point.fiber.obj W)] :
    ∃ C : (geomPtAt x).point.fiber.obj W → Set (Up (fpt x t) W), (∀ b, IsClopen (C b)) ∧
      (∀ u, ∃! b, u ∈ C b) ∧ (∀ b, κp (fpt x t) W (sx (fpt x t) W (τ b) default) ∈ C b) := by
  classical
  have : IsAffine ((𝟭 Scheme).obj W.left) := inferInstanceAs (IsAffine W.left)
  choose Cn hCn hCnp using fun b => exists_clopen_lift (pullback.snd (f0 T (fpt x t)) W.hom)
    ⟨_, isOpen_range_sx (fpt x t) W (τ b)⟩ (isClosed_range_sx (fpt x t) W (τ b))
  have hmem : ∀ b e, (pullback.snd (f0 T (fpt x t)) W.hom).toNormalization e ∈ Cn b ↔
      e ∈ Set.range (sx (fpt x t) W (τ b)) := fun b e =>
    Iff.of_eq (congrArg (fun O : (Xp (fpt x t) W).Opens => e ∈ O) (hCnp b))
  have hd := (pullback.snd (f0 T (fpt x t)) W.hom).toNormalization.denseRange
  have hpart : ∀ n : Nn (fpt x t) W, ∃! b, n ∈ Cn b := by
    intro n
    have hex : ∃ b, n ∈ Cn b := by
      by_contra hne
      simp only [not_exists] at hne
      have hO : IsOpen (⋃ b, (Cn b : Set (Nn (fpt x t) W)))ᶜ :=
        (isClosed_iUnion_of_finite fun b => (hCn b).isClosed).isOpen_compl
      obtain ⟨e, he⟩ := hd.exists_mem_open hO ⟨n, by
        simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
        exact hne⟩
      obtain ⟨b, hb⟩ := sx_cover W x t τ hτ e
      exact he (Set.mem_iUnion.2 ⟨b, (hmem b e).2 hb⟩)
    obtain ⟨b, hb⟩ := hex
    refine ⟨b, hb, fun b' hb' => ?_⟩
    obtain ⟨e, he1, he2⟩ := hd.exists_mem_open ((hCn b).isOpen.inter (hCn b').isOpen) ⟨n, hb, hb'⟩
    obtain ⟨z, hz⟩ := (hmem b e).1 he1
    obtain ⟨z', hz'⟩ := (hmem b' e).1 he2
    refine (sx_disj W x t τ hτ b b' ?_).symm
    calc sx (fpt x t) W (τ b) default = sx (fpt x t) W (τ b) z := by rw [Subsingleton.elim z default]
      _ = e := hz
      _ = sx (fpt x t) W (τ b') z' := hz'.symm
      _ = sx (fpt x t) W (τ b') default := by rw [Subsingleton.elim z' default]
  refine ⟨fun b => ψn (fpt x t) W ⁻¹' (Cn b), fun b => (hCn b).preimage (ψn (fpt x t) W).continuous,
    fun u => ?_, fun b => ?_⟩
  · obtain ⟨b, hb, hu⟩ := hpart (ψn (fpt x t) W u)
    exact ⟨b, hb, hu⟩
  · show ψn (fpt x t) W (κp (fpt x t) W (sx (fpt x t) W (τ b) default)) ∈ Cn b
    rw [← Scheme.Hom.comp_apply, κp_ψn]
    exact (hmem b _).2 ⟨default, rfl⟩

end RamanujanPetersson.EtPBC.GenGeo

end

end

-- ===== S4.Def_RP_EtPBC_A_EG =====
section

/-!
# S4-EtPBC-A, M4(E), EG: relations of the sections `f_j` are relations of the generators near `ξ`

* `dT ξ : Spec κ(ξ) ⟶ T ×_P Y` (the diagonal point), `dT_map`: its images in `W ×_P Y` are the sheet points;
* `exists_fib_preimage`: a point of `T ×_P Y` over `fpt t'` is `fibToNbhd ⟨T, t'⟩ q` for some `q`;
* **`eg_rel`**: at a point `x = T.hom v` with `ξ ⤳ v`, every relation of the `f_j` is a relation of the `z_j`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.GenGeo

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech GenAlg

universe u

variable {P : Scheme.{u}} {T : P.Etale} (ξ : T.left)

section Rel

variable {Λ : Type u} [CommRing Λ] (F : EtSh Λ P) {J : Type u} (W : J → P.Etale)
  (z : ∀ j, F.obj.obj (op (W j))) (η : P)

/-- **EG: near `ξ`, relations of the `f_j` are relations of the `z_j`.** -/
theorem eg_rel [∀ j, IsAffine (W j).left] (t : (geomPtAt η).point.fiber.obj T)
    (τ : ∀ p : FibPts η W, T ⟶ W p.1) (hτ : ∀ p, (geomPtAt η).point.fiber.map (τ p) t = p.2)
    [IsFinite (πn T (fpt η t))]
    (hgood : ∀ c, GenAlg.rel W F z η c = 0 → gsum F z τ c = 0)
    (C : ∀ p : FibPts η W, Set (Up (fpt η t) (W p.1))) (hCcl : ∀ p, IsClosed (C p))
    (hd : ∀ p, κp (fpt η t) (W p.1) (sx (fpt η t) (W p.1) (τ p) default) ∈ C p)
    (f : ∀ j, (constSh Λ (Yn T (fpt η t)) (Mq F W z η)).obj.obj (op ((etPull (πn T (fpt η t))).obj (W j))))
    (hf : ∀ p u, u ∈ C p → cval (f p.1) u = mkv F W z η p)
    (v : T.left) (hsp : fpt η t ⤳ v) (l : FibPts (T.hom v) W →₀ Λ)
    (hl : GenAlg.rel W ((push (πn T (fpt η t)) Λ).obj (constSh Λ (Yn T (fpt η t)) (Mq F W z η))) f (T.hom v) l = 0) :
    GenAlg.rel W F z (T.hom v) l = 0 := by
  classical
  obtain ⟨t', ht'⟩ := exists_fib_over T v
  have hs : fpt η t ⤳ fpt (T.hom v) t' := ht'.symm ▸ hsp
  have hb : ∀ p : FibPts (T.hom v) W, ∃ b, p.2 = (geomPtAt (T.hom v)).point.fiber.map (τ ⟨p.1, b⟩) t' :=
    fun p => exists_eq_tau η t (fun b => τ ⟨p.1, b⟩) (fun b => hτ ⟨p.1, b⟩) (T.hom v) t' hs p.2
  choose bsel hbsel using hb
  let φ : FibPts (T.hom v) W → FibPts η W := fun p => ⟨p.1, bsel p⟩
  let c' : FibPts η W →₀ Λ := Finsupp.linearCombination Λ (fun p => Finsupp.single (φ p) (1 : Λ)) l
  have hgerm : GenAlg.germ F (T.hom v) t' (gsum F z τ c') = GenAlg.rel W F z (T.hom v) l := by
    have e1 : gsum F z τ c' = Finsupp.linearCombination Λ
        (fun p : FibPts (T.hom v) W => (F.obj.map (τ (φ p)).op).hom (z p.1)) l := by
      refine (Finsupp.apply_linearCombination Λ (gsum F z τ) _ l).trans ?_
      refine congrArg (fun v => Finsupp.linearCombination Λ v l) (funext fun p => ?_)
      show gsum F z τ (Finsupp.single (φ p) 1) = _
      rw [gsum, Finsupp.linearCombination_single, one_smul]
    rw [e1]
    refine (Finsupp.apply_linearCombination Λ
      ((geomPtAt (T.hom v)).point.toPresheafFiber T t' F.obj).hom _ l).trans ?_
    refine congrArg (fun v => Finsupp.linearCombination Λ v l) (funext fun p => ?_)
    exact (germ_map F (T.hom v) (τ (φ p)) t' (z p.1)).trans
      (congrArg (fun b => GenAlg.germ F (T.hom v) b (z p.1)) (hbsel p).symm)
  rw [← hgerm]
  suffices hq : Submodule.mkQ (LinearMap.ker (GenAlg.rel W F z η)) c' = 0 by
    rw [hgood c' (LinearMap.mem_ker.1 ((Submodule.Quotient.mk_eq_zero _).1 hq))]
    exact map_zero ((geomPtAt (T.hom v)).point.toPresheafFiber T t' F.obj).hom
  -- a point of the fibre in the closure of the diagonal point
  have hfin : IsFinite (pullback.fst T.hom (πn T (fpt η t))) := inferInstance
  have hcl := IsClosedMap.closure_image_eq_of_continuous (pullback.fst T.hom (πn T (fpt η t))).isClosedMap
    (pullback.fst T.hom (πn T (fpt η t))).continuous {dT (fpt η t) default}
  have hξ : pullback.fst T.hom (πn T (fpt η t)) (dT (fpt η t) default) = fpt η t := by
    rw [← Scheme.Hom.comp_apply, dT, pullback.lift_fst, Scheme.fromSpecResidueField_apply]
  have hv : v ∈ closure ((pullback.fst T.hom (πn T (fpt η t))) '' {dT (fpt η t) default}) := by
    rw [Set.image_singleton, hξ]
    exact specializes_iff_mem_closure.1 hsp
  rw [hcl] at hv
  obtain ⟨zz, hzz, hzv⟩ := hv
  obtain ⟨q, hq⟩ := exists_fib_preimage (fpt η t) (T.hom v) t' zz (hzv.trans ht'.symm)
  have hterm : ∀ p : FibPts (T.hom v) W, cval (M := Mq F W z η) (f p.1)
      (fibToNbhd (πn T (fpt η t)) (geomPtAt (T.hom v)) ⟨W p.1, p.2⟩ q) = mkv F W z η (φ p) := by
    intro p
    let a : (geomPtAt (T.hom v)).point.fiber.elementsMk T t' ⟶
        (geomPtAt (T.hom v)).point.fiber.elementsMk (W p.1) p.2 := ⟨τ (φ p), (hbsel p).symm⟩
    have h1 := congrArg (fun φ => φ.base q) (fibToNbhd_map (πn T (fpt η t)) (geomPtAt (T.hom v)) a)
    have h2 : fibToNbhd (πn T (fpt η t)) (geomPtAt (T.hom v)) ⟨W p.1, p.2⟩ q =
        ((etPull (πn T (fpt η t))).map (τ (φ p))).left zz :=
      h1.symm.trans ((Scheme.Hom.comp_apply _ _ q).trans (congrArg _ hq))
    have hsp2 : dT (fpt η t) default ⤳ zz := specializes_iff_mem_closure.2 hzz
    have h3 : ((etPull (πn T (fpt η t))).map (τ (φ p))).left (dT (fpt η t) default) =
        κp (fpt η t) (W p.1) (sx (fpt η t) (W p.1) (τ (φ p)) default) :=
      (Scheme.Hom.comp_apply _ _ _).symm.trans ((congrArg (fun φ => φ.base default) (dT_map (fpt η t) (τ (φ p)))).trans
        (Scheme.Hom.comp_apply _ _ _))
    have hmem : ((etPull (πn T (fpt η t))).map (τ (φ p))).left zz ∈ C (φ p) :=
      (hsp2.map ((etPull (πn T (fpt η t))).map (τ (φ p))).left.continuous).mem_closed (hCcl (φ p))
        (h3 ▸ hd (φ p))
    exact (congrArg (cval (f p.1)) h2).trans (hf (φ p) _ hmem)
  have hsum := (psi_rel (πn T (fpt η t)) W f (T.hom v) l q).symm.trans
    ((congrArg (fun e => psi (πn T (fpt η t)) (geomPtAt (T.hom v)) e q) hl).trans (psi_zero _ _ q))
  calc Submodule.mkQ (LinearMap.ker (GenAlg.rel W F z η)) c'
      = l.sum (fun p c => c • mkv F W z η (φ p)) := by
        rw [Finsupp.apply_linearCombination, Finsupp.linearCombination_apply]
        rfl
    _ = l.sum fun p c => c • cval (M := Mq F W z η) (f p.1)
          (fibToNbhd (πn T (fpt η t)) (geomPtAt (T.hom v)) ⟨W p.1, p.2⟩ q) :=
        Finsupp.sum_congr fun p _ => by rw [hterm p]
    _ = 0 := hsum

end Rel

end RamanujanPetersson.EtPBC.GenGeo

end

end

-- ===== S4.Def_RP_EtPBC_A_CovNbB =====
section

/-!
# S4-EtPBC-A, R4-T2 (G2): the cover lifting property at a neighbourhood gives `LiftT`

* `g_main`: the abstract pullback bookkeeping (no heavy terms): an iso `κ : P' ×_P Y ≅ Y_V'`, a finite surjective
  `ρ' : U' ⟶ Y_V'`, a retract `e, e'` of `Y_s` and a lift `ψ'` over `Y_x` give the `LiftT` tail;
* `surj_χ'`, `isClosedImmersion_xL`: the lift `Spec K ⟶ Spec R'` of `x` is a closed immersion;
* **`liftT_core`**, **`liftT_of_coverLiftAt`**: `CoverLiftAt` at `xV` gives `T2.LiftT (qV K gK) s π`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.Cov

universe u

section Gen

end Gen

section Aux

end Aux

section Chi

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN algKY algT CoverLift.cR CoverLift.aR CoverLift.eR CoverLift.c₀ CoverLift.c₁ CoverLift.c₀₁ CoverLift.a₀ CoverLift.a₁ CoverLift.a₀₁ CoverLift.f₀ CoverLift.f₁ CoverLift.et₀ CoverLift.et₁

variable {K : Type u} [Field K] {V : Scheme.{u}} {gV : V ⟶ Spec (CommRingCat.of K)} {Y : Scheme.{u}}
  {π : Y ⟶ PV K gV} {x : Spec (CommRingCat.of K) ⟶ V} {hx : x ≫ gV = 𝟙 _}
  {T : Scheme.{u}} {q : T ⟶ Yx K gV π x} (L : LiftD K gV π x q hx)

theorem surj_χ' : letI := algKV K gV; Function.Surjective L.χ' := by
  letI := algKV K gV
  intro c
  refine ⟨algebraMap Γ(V, ⊤) L.R' (algebraMap K Γ(V, ⊤) c), ?_⟩
  rw [L.hχ, AlgHom.commutes]
  rfl

theorem isClosedImmersion_xL [IsAffine V] [IsFinite π] [IsAffineHom q] : IsClosedImmersion (xL L) := by
  letI := algKV K gV
  exact IsClosedImmersion.spec_of_surjective _ (surj_χ' L)

end Chi

section Main

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN algKY algT CoverLift.cR CoverLift.aR CoverLift.eR CoverLift.c₀ CoverLift.c₁ CoverLift.c₀₁ CoverLift.a₀ CoverLift.a₁ CoverLift.a₀₁ CoverLift.f₀ CoverLift.f₁ CoverLift.et₀ CoverLift.et₁

end Main

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_O2MV =====
section

/-!
# S4-EtPBC-A, O2 (MV route), MV: the Mayer-Vietoris sequence of free sheaves

For a commutative square `p₁ ≫ w = p₂ ≫ v` of `P.Etale` (`W' ⟶ W, U ⟶ Z`):
* `freeMap_comp`; `stalk_freeMap_injective`/`_surjective` (fibre map injective/surjective ⇒ stalk map so);
* `mvC`: the short complex `Λ[W'] ⟶ Λ[W] ⊞ Λ[U] ⟶ Λ[Z]` (maps `(Λ[p₁], -Λ[p₂])`, `Λ[w] + Λ[v]`);
* **`mvC_shortExact`**: short exact when every fibre of `Z` is subsingleton and at every point either the fibre of
  `W` is a singleton and `p₂` is bijective on fibres, or the fibre of `U` is a singleton and `p₁` is so;
* **`mv_exists`**: a class `β ∈ Ext^{n+1}(Λ[Z], F)` killed by `Λ[w]` and `Λ[v]` is `ε.comp κ`, `κ ∈ Ext^n(Λ[W'], F)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.GenAlg
  RamanujanPetersson.EtPBC.FreeStk

universe u

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}

section Stalks

variable {W' W U Z : P.Etale} (p₁ : W' ⟶ W) (p₂ : W' ⟶ U) (w : W ⟶ Z) (v : U ⟶ Z)

theorem mvC_f_injective (x : P)
    (hx : Function.Injective ((geomPtAt x).point.fiber.map p₁) ∨
      Function.Injective ((geomPtAt x).point.fiber.map p₂)) :
    Function.Injective (((geomPtAt x).stalkF Λ).map (biprod.lift (freeMap Λ p₁) (-freeMap Λ p₂))).hom := by
  intro z z' h
  rcases hx with h1 | h2
  · apply stalk_freeMap_injective p₁ x h1
    have := congrArg (((geomPtAt x).stalkF Λ).map biprod.fst).hom h
    rwa [stalk_comp_apply, stalk_comp_apply, biprod.lift_fst] at this
  · apply stalk_freeMap_injective p₂ x h2
    have := congrArg (((geomPtAt x).stalkF Λ).map biprod.snd).hom h
    rwa [stalk_comp_apply, stalk_comp_apply, biprod.lift_snd, Functor.map_neg, ModuleCat.hom_neg,
      LinearMap.neg_apply, LinearMap.neg_apply, neg_inj] at this

theorem mvC_exact_stalk (x : P) [Subsingleton ((geomPtAt x).point.fiber.obj Z)]
    (hx : (Subsingleton ((geomPtAt x).point.fiber.obj W) ∧ Function.Bijective ((geomPtAt x).point.fiber.map p₂)) ∨
      (Subsingleton ((geomPtAt x).point.fiber.obj U) ∧ Function.Bijective ((geomPtAt x).point.fiber.map p₁)))
    (y : stalk Λ (freeSh Λ W ⊞ freeSh Λ U) x)
    (hy : (((geomPtAt x).stalkF Λ).map (biprod.desc (freeMap Λ w) (freeMap Λ v))).hom y = 0) :
    ∃ l, (((geomPtAt x).stalkF Λ).map (biprod.lift (freeMap Λ p₁) (-freeMap Λ p₂))).hom l = y := by
  obtain ⟨p, hp⟩ := freeLin_surjective W x ((((geomPtAt x).stalkF Λ).map biprod.fst).hom y)
  obtain ⟨q, hq⟩ := freeLin_surjective U x ((((geomPtAt x).stalkF Λ).map biprod.snd).hom y)
  have hR : (((geomPtAt x).stalkF Λ).map (biprod.desc (freeMap Λ w) (freeMap Λ v))).hom y =
      freeLin Λ Z x (Finsupp.mapDomain ((geomPtAt x).point.fiber.map w) p +
        Finsupp.mapDomain ((geomPtAt x).point.fiber.map v) q) := by
    have e1 : ∀ a, (((geomPtAt x).stalkF Λ).map (biprod.desc (freeMap Λ w) (freeMap Λ v))).hom
        ((((geomPtAt x).stalkF Λ).map biprod.inl).hom a) = (((geomPtAt x).stalkF Λ).map (freeMap Λ w)).hom a :=
      fun a => by rw [stalk_comp_apply, biprod.inl_desc]
    have e2 : ∀ a, (((geomPtAt x).stalkF Λ).map (biprod.desc (freeMap Λ w) (freeMap Λ v))).hom
        ((((geomPtAt x).stalkF Λ).map biprod.inr).hom a) = (((geomPtAt x).stalkF Λ).map (freeMap Λ v)).hom a :=
      fun a => by rw [stalk_comp_apply, biprod.inr_desc]
    conv_lhs => rw [stalk_biprod_eq x y]
    rw [map_add, e1, e2, ← hp, ← hq, freeLin_natural, freeLin_natural, map_add]
  rw [hR] at hy
  have hpq := freeLin_injective Z x (hy.trans (map_zero (freeLin Λ Z x)).symm)
  have hε : aug Λ _ p + aug Λ _ q = 0 := by
    have := congrArg (aug Λ _) hpq
    rwa [map_add, aug_mapDomain, aug_mapDomain, map_zero] at this
  rcases hx with ⟨hW, hb⟩ | ⟨hU, ha⟩
  · let e := Equiv.ofBijective _ hb
    have he : (geomPtAt x).point.fiber.map p₂ ∘ e.symm = id := funext fun b => e.apply_symm_apply b
    refine ⟨freeLin Λ W' x (Finsupp.mapDomain e.symm (-q)), stalk_biprod_ext x ?_ ?_⟩
    · rw [stalk_comp_apply, biprod.lift_fst, freeLin_natural, ← hp]
      congr 1
      apply eq_of_aug_eq
      rw [aug_mapDomain, aug_mapDomain, map_neg]
      linear_combination -hε
    · rw [stalk_comp_apply, biprod.lift_snd, Functor.map_neg, ModuleCat.hom_neg, LinearMap.neg_apply,
        freeLin_natural, ← hq, ← Finsupp.mapDomain_comp, he, Finsupp.mapDomain_id, map_neg, neg_neg]
  · let e := Equiv.ofBijective _ ha
    have he : (geomPtAt x).point.fiber.map p₁ ∘ e.symm = id := funext fun b => e.apply_symm_apply b
    refine ⟨freeLin Λ W' x (Finsupp.mapDomain e.symm p), stalk_biprod_ext x ?_ ?_⟩
    · rw [stalk_comp_apply, biprod.lift_fst, freeLin_natural, ← hp, ← Finsupp.mapDomain_comp, he,
        Finsupp.mapDomain_id]
    · rw [stalk_comp_apply, biprod.lift_snd, Functor.map_neg, ModuleCat.hom_neg, LinearMap.neg_apply,
        freeLin_natural, ← hq, ← map_neg]
      congr 1
      apply eq_of_aug_eq
      rw [map_neg, aug_mapDomain, aug_mapDomain]
      linear_combination -hε

end Stalks

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2P1 =====
section

/-!
# S4-EtPBC-A, O2 M5 P1: purity for Kummer roots on a Dedekind domain (field theory)

`B` Dedekind with fraction field `K`, `Bt = B[1/t]`, `(t)` prime.

* `locPt p hp`: the height-one prime `p Bt` of a localization; `valuation_locPt` (same valuation on `K`);
* `dvd_log_of_mem_maxUnram`: a root `α ∈ maxUnram Bt K` of `u ∈ K` gives `d ∣ log v_p(u)` for `t ∉ p`;
* `valuation_algebraMap_bot`, `root_mem_maxUnram_self`: `d ∣ log v(u)` at every height-one prime of `B` puts every
  `d`-th root of `u` in `maxUnram B K` (`root_mem_maxUnram_of_dvd` with `M = ⊥`, model `B`);
* `exists_root_unit`: `d`-th roots of units of `B` lie in `maxUnram B K`;
* **`root_mem_maxUnram_twist`**: for `α ∈ maxUnram Bt K` with `α ^ d = u`, there is `m : ℤ` such that every `d`-th root
  of `u t^m` lies in `maxUnram B K`.
-/

set_option autoImplicit false

open IsDedekindDomain

noncomputable section

namespace RamanujanPetersson.EtCompact.Pur

open RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer

section VC

end VC

section Root

end Root

section Twist

variable {B Bt K : Type} [CommRing B] [IsDedekindDomain B] [CommRing Bt] [IsDedekindDomain Bt] [Algebra B Bt]
  {t : B} [IsLocalization.Away t Bt] (ht : t ≠ 0) (hP : (Ideal.span {t}).IsPrime)
  [Field K] [Algebra B K] [Algebra Bt K] [IsScalarTower B Bt K] [IsFractionRing B K] [IsFractionRing Bt K]

include ht hP in
/-- **Purity for Kummer roots**: for `α ∈ maxUnram Bt K` with `α ^ d = u` (`u ≠ 0`), every `d`-th root of
`u t^m`, `m = log v_t(u)`, lies in `maxUnram B K`. -/
theorem root_mem_maxUnram_twist {d : ℕ} [NeZero d] (hd : IsUnit (d : B)) {α : AlgebraicClosure K}
    (hα : α ∈ maxUnram Bt K) {u : K} (hu0 : u ≠ 0) (hu : α ^ d = algebraMap K (AlgebraicClosure K) u) :
    ∃ m : ℤ, ∀ γ : AlgebraicClosure K, γ ^ d = algebraMap K (AlgebraicClosure K) (u * algebraMap B K t ^ m) →
      γ ∈ maxUnram B K := by
  have hS : Submonoid.powers t ≤ nonZeroDivisors B :=
    powers_le_nonZeroDivisors_of_noZeroDivisors ht
  have htK : algebraMap B K t ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective B K)).2 ht
  let w : HeightOneSpectrum B := ⟨Ideal.span {t}, hP, by rwa [Ne, Ideal.span_singleton_eq_bot]⟩
  refine ⟨WithZero.log (w.valuation K u), fun γ hγ => root_mem_maxUnram_self hd
    (mul_ne_zero hu0 (zpow_ne_zero _ htK)) (fun v => ?_) hγ⟩
  have hvu : v.valuation K u ≠ 0 := (Valuation.ne_zero_iff _).2 hu0
  have hvt : v.valuation K (algebraMap B K t) ≠ 0 := (Valuation.ne_zero_iff _).2 htK
  rw [map_mul, map_zpow₀, WithZero.log_mul hvu (zpow_ne_zero _ hvt), WithZero.log_zpow]
  by_cases hv : t ∈ v.asIdeal
  · have hvw : v = w := by
      refine HeightOneSpectrum.ext ((w.isMaximal.eq_of_le v.isPrime.ne_top ?_).symm)
      exact (Ideal.span_singleton_le_iff_mem _).2 hv
    subst hvw
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_singleton _ ht rfl,
      WithZero.log_exp, smul_eq_mul, mul_neg_one, add_neg_cancel]
    exact dvd_zero _
  · have hdisj : Disjoint (Submonoid.powers t : Set B) v.asIdeal := by
      rw [Set.disjoint_left]
      rintro _ ⟨k, rfl⟩ hk
      exact hv (v.isPrime.mem_of_pow_mem k hk)
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hv,
      WithZero.log_one, smul_zero, add_zero]
    exact dvd_log_of_mem_maxUnram (Submonoid.powers t) hS hα hu v hdisj

end Twist

end RamanujanPetersson.EtCompact.Pur

end

end

-- ===== S4.Def_RP_EtPBC_A_O2PPTd =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2PPTd): the chart form of the piece transfer, and Zariski shrinks

For chart neighbourhoods `D = chEt c φ`, `D₁ = chEt c φ₁` and any `dm : D₁ ⟶ D` in `P.Etale`:
* `left_spec_map`: `dm.left ≫ Spec.map φ = Spec.map φ₁`; **`shG_wm`**: `wm (prdMap dm) ≫ shG c φ = shG c φ₁`;
* `sXW c φ R ζ0 ∈ Γ(W)` (the image of `ζ0 ∈ k`), `ζW_eq`, **`wm_appTop_sXW`**;
* **`locCls_kapS_chart`**: `locCls_kapS_shrink` (O2PPTc) with the roots of unity `ζW` of O2Km9a on both sides;
* **`piece_unique_away`**: if `Γ(X₁) = Γ(X)[1/s]` along `f`, at most one piece of `X₁` lies over a piece of `X`
  (applies to `toDF` by `isLocalization_away_toDF`, O2ZarCh).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.EtShap RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtCompact.Pur
  RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer RamanujanPetersson.EtCompact.GalTrE

section Away

end Away

section Chart

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c]
  {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)]
  {B₁ : CommRingCat.{0}} (φ₁ : CommRingCat.of k[X] ⟶ B₁) [Etale (Spec.map φ₁ ≫ c)]
  {Uo : P.Opens} (R : P.Etale) [IsAffine R.left] (dm : chEt c φ₁ ⟶ chEt c φ)

set_option backward.isDefEq.respectTransparency false in
theorem wm_appTop_sXW (ζ0 : k) : (wm (R := R) (prdMap dm (opEt Uo))).appTop (sXW c φ R ζ0) = sXW c φ₁ R ζ0 := by
  unfold sXW
  rw [← shG_wm c φ φ₁ R dm]
  rfl

end Chart

section ChartPPT

end ChartPPT

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl2b =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl2b): the charts of stage S3

GLOB/REL PLAN v1, stage S3 (geometric part). `D_G := chEt c (k[X] ⟶ k[X]_G)` for `G = g₀ c₀' t` (`g₀ ∣ G`,
`t = X - a ∣ G`):
* `toDG : D_G ⟶ D_{g₀}`; `chG_mem`: `D_G` lies over `U₀` (no point over `z`), so `opnDg c G ≤ U₀`;
* `sigG : opEt (c(D(G))) ⟶ D_G ×_P U₀` and `mG := toOpEt ≫ sigG` (the map `m` of `uk_diff`), `mG_prT` (`hm`),
  `mG_prdMap` (`m ≫ (D_G ⟶ D_{g₀}) = (D₂ ⟶ D_{g₀})`, maps into `D ×_P X` are determined by `prT` for `D` open);
* `gamMap_shG`, `appTop_gamMap`, `isUnit_rho`: a divisor of `G^n` in `Γ(Y₀)` becomes a unit on `Y₁ = (D_G ×_P U₀) ×_P R`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap
  RamanujanPetersson.EtPBC.EtDeg

section Mono

end Mono

section ChG

end ChG

section Sec

end Sec

section Gam

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c] {Uo : P.Opens}
  (R : P.Etale) [IsAffine R.left]

variable {g₀ G : k[X]} (hG₀ : g₀ ∣ G)
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).left]
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).left]

/-- **A divisor of `r` (`r` a unit on `D_G`) in `Γ(Y₀)` becomes a unit on `Y₁`.** -/
theorem isUnit_rho {x : Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)}
    {r : k[X]} (hx : x ∣ gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R) r)
    (hr : IsUnit ((locF (B := CommRingCat.of k[X]) G).hom r)) :
    IsUnit ((wm (R := R) (prdMap (toDG c hG₀) (opEt Uo))).appTop x) := by
  have e := appTop_gamMap (wm (R := R) (prdMap (toDG c hG₀) (opEt Uo)))
    (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R) (shG c (locF (B := CommRingCat.of k[X]) G) (Uo := Uo) R)
    (shG_wm c _ _ R (toDG c hG₀)) r
  refine isUnit_of_dvd_unit (map_dvd (wm (R := R) (prdMap (toDG c hG₀) (opEt Uo))).appTop.hom hx) ?_
  rw [e, gamMap_shG]
  exact hr.map _

end Gam

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl2d =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl2d): stage S4, the global unit `H` seen on `W₂`

GLOB/REL PLAN v1, stage S4 (ring level). `ρ := (wm (prdMap (toDG c hG₀) (opEt U₀))).appTop : Γ(Y₀) → Γ(Y₁)`,
`m := mG c hle D₂ hD₂` (O2Gl2b), `D₂ = chEt c φ₂`, `d : D₂ ⟶ D_{g₀}`:
* `prdMap_comp`, `wm_prdMap_comp_appTop`: `prdMap` is functorial (target an open chart);
* `wm_mG_appTop`: `m^* ∘ ρ = (prdMap d)^*`; `wm_mG_gamMap`: `m^* ρ (r) = bW (φ₂ r)` for `r ∈ k[X]`;
* `exists_Hg`: `H := ũ' t^{-N}` is a unit; **`wm_mG_H`**: `m^* H · bW(φ₂ t)^N = (prdMap d)^* ũ'`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap
  RamanujanPetersson.EtPBC.EtDeg

section Fun

end Fun

section H

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c] {Uo : P.Opens}
  (R : P.Etale) [IsAffine R.left] {g₀ G : k[X]} (hG₀ : g₀ ∣ G) (hle : opnDg c G ≤ Uo)
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).left]
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).left]
  {B₂ : CommRingCat.{0}} (φ₂ : CommRingCat.of k[X] ⟶ B₂) [Etale (Spec.map φ₂ ≫ c)]
  [IsAffine (prd (chEt c φ₂) (opEt Uo)).left]
  (hD₂ : ∀ v : (prd (chEt c φ₂) (opEt Uo)).left, (prd (chEt c φ₂) (opEt Uo)).hom v ∈ opnDg c G)
  (d : chEt c φ₂ ⟶ chEt c (locF (B := CommRingCat.of k[X]) g₀))

include d in
theorem wm_mG_gamMap (r : k[X]) :
    (wm (R := R) (mG c hle (chEt c φ₂) hD₂)).appTop ((wm (R := R) (prdMap (toDG c hG₀) (opEt Uo))).appTop
      (gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R) r)) =
      (bW (Spec.map φ₂ ≫ c) (opEt Uo) R).hom (φ₂.hom r) := by
  rw [wm_mG_appTop c R hG₀ hle φ₂ hD₂ d,
    appTop_gamMap _ _ (shG c φ₂ (Uo := Uo) R) (shG_wm c _ φ₂ R d) r, gamMap_shG]

end H

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl2h =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl2h): stage S4 on the charts, the data `e`, `g`, `hHp`, `hHq` of `uk_diff`

GLOB/REL PLAN v1, stage S4. `d = d₂₁ ≫ d₀ : D₂ ⟶ D₁ ⟶ D_{g₀}` with `Γ(W₂) = Γ(W₁)[1/s]` along `d₂₁` (Zariski) and
`d₂₁.left = Spec.map ι`; `H · ρ(r)^N = ρ y` on `Y₁`, `(prdMap d₀)^* y = r^N ũ (1 - r z)` in `Π_q Frac(Γ(W₁) ⧸ q)`
(`ũ = (u₁ on p₁, 1 elsewhere)`, `z` integral over `B₁`):
* **`exists_S4`**: `e`, a monic `g ∈ B₂[X]` of positive degree with `g(e q) = 0` (`he`), and for the piece `p₂` over `p₁`:
  `m^* H = Ψ u₁ (1 + bK(φ₂ r) e p₂)` (`hHp`, any compatible `Ψ`), `m^* H = 1 + bK(φ₂ r) e q` for `q ≠ p₂` (`hHq`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap
  RamanujanPetersson.EtPBC.EtDeg

section S4GenB

end S4GenB

section S4

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c] {Uo : P.Opens}
  (R : P.Etale) [IsAffine R.left] {g₀ G : k[X]} (hG₀ : g₀ ∣ G) (hle : opnDg c G ≤ Uo)
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).left]
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).left]
  {B₁ : CommRingCat.{0}} (φ₁ : CommRingCat.of k[X] ⟶ B₁) [Etale (Spec.map φ₁ ≫ c)]
  [IsAffine (prd (chEt c φ₁) (opEt Uo)).left]
  {B₂ : CommRingCat.{0}} (φ₂ : CommRingCat.of k[X] ⟶ B₂) [Etale (Spec.map φ₂ ≫ c)]
  [IsAffine (prd (chEt c φ₂) (opEt Uo)).left]
  (hD₂ : ∀ v : (prd (chEt c φ₂) (opEt Uo)).left, (prd (chEt c φ₂) (opEt Uo)).hom v ∈ opnDg c G)
  (d₂₁ : chEt c φ₂ ⟶ chEt c φ₁) (d₀ : chEt c φ₁ ⟶ chEt c (locF (B := CommRingCat.of k[X]) g₀))

/-- `(prdMap d₂₁)^*` carries `r` on `W₁` to `bW(φ₂ r)` on `W₂`. -/
theorem wm_gamMap₂ (r : k[X]) :
    (wm (R := R) (prdMap d₂₁ (opEt Uo))).appTop (gamMap (shG c φ₁ (Uo := Uo) R) r) =
      (bW (Spec.map φ₂ ≫ c) (opEt Uo) R).hom (φ₂.hom r) :=
  (appTop_gamMap _ _ (shG c φ₂ (Uo := Uo) R) (shG_wm c φ₁ φ₂ R d₂₁) r).trans (gamMap_shG c R φ₂ r)

end S4

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2LocU =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2LocU): changing the open of a one-point MV class

GLOB/REL PLAN v1 (4). For `U₁ ≤ U₀ ≤ Uz` and `D : P.Etale`:
* `locC_opn`: `ε(D, U₁ ≤ Uz) ∘ Λ[prdMapR D (opEtMap h₁₀)] = ε(D, U₀ ≤ Uz)`;
* `locCls_opn`: `ε(D, U₀) ∘ κ = ε(D, U₁) ∘ Λ[prdMapR] ∘ κ`;
* **`locCls_opn_map`**: `ε(D, U₀) ∘ Λ[m] ∘ κ = ε(D, U₁) ∘ Λ[m'] ∘ κ` when `prdMapR ≫ m = m'`;
* **`locCls_opn_toOpEt`**: for `σ : opEt U₁ ⟶ T` and `D ×_P U₀` over `U₁`:
  `ε(D, U₀) ∘ Λ[toOpEt ≫ σ] ∘ κ = ε(D, U₁) ∘ Λ[prT ≫ σ] ∘ κ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtCompact.CurveHn RamanujanPetersson.EtPBC.GenGeo

universe u

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}

section LocU

variable {U₁ U₀ Uz : P.Opens} (h₁₀ : U₁ ≤ U₀) (h : U₀ ≤ Uz) (h₁ : U₁ ≤ Uz) (D : P.Etale)

/-- **LocU**: `ε(D, U₀) ∘ Λ[m] ∘ κ = ε(D, U₁) ∘ Λ[m'] ∘ κ` when `prdMapR ≫ m = m'`. -/
theorem locCls_opn_map (hS₁ : (locC Λ D h₁).ShortExact) (hS : (locC Λ D h).ShortExact) {T : P.Etale}
    (m : prd D (opEt U₀) ⟶ T) (m' : prd D (opEt U₁) ⟶ T) (hm : prdMapR D (opEtMap h₁₀) ≫ m = m')
    {F : EtSh Λ P} (κ : Ext.{u} (freeSh Λ T) F 1) :
    hS.extClass.comp ((Ext.mk₀ (freeMap Λ m)).comp κ (zero_add 1)) (show 1 + 1 = 2 from rfl) =
      hS₁.extClass.comp ((Ext.mk₀ (freeMap Λ m')).comp κ (zero_add 1)) (show 1 + 1 = 2 from rfl) := by
  rw [locCls_opn h₁₀ h h₁ D hS₁ hS, Ext.mk₀_comp_mk₀_assoc, ← freeMap_comp, hm]

end LocU

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2PP4b =====
section

/-!
# S4-EtPBC-A, O2 PP' (O2PP4b): chart helpers for the S1 layer

* `exists_hj_pair'`: `exists_hj_pair` (O2PP4a) with `u = x / y` given as an equation;
* `isUnit_locF_comp_of_dvd`: `r ∣ F` is a unit on `D_{φ F}`;
* `wm_gamMap_pow_mul`: `(wm (prdMap dm))^*` of `r = t^e r'` along `shG`;
* `isUnit_gamMap_shG`: units of `B₁` stay units on `W₁`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap
  RamanujanPetersson.EtPBC.EtDeg

section HJ'

end HJ'

section ChartS1

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c]
  {Uo : P.Opens} (R : P.Etale) [IsAffine R.left] {a : k}

theorem wm_gamMap_pow_mul {B B₁ : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)]
    (φ₁ : CommRingCat.of k[X] ⟶ B₁) [Etale (Spec.map φ₁ ≫ c)]
    [IsAffine (prd (chEt c φ) (opEt Uo)).left] [IsAffine (prd (chEt c φ₁) (opEt Uo)).left]
    (dm : chEt c φ₁ ⟶ chEt c φ) {r r' : k[X]} {e : ℕ} (hr : r = (X - C a) ^ e * r') :
    (wm (R := R) (prdMap dm (opEt Uo))).appTop.hom (gamMap (shG c φ (Uo := Uo) R) r) =
      gamMap (shG c φ₁ (Uo := Uo) R) (X - C a) ^ e * gamMap (shG c φ₁ (Uo := Uo) R) r' := by
  have h0 := appTop_gamMap (wm (R := R) (prdMap dm (opEt Uo))) (shG c φ (Uo := Uo) R) (shG c φ₁ (Uo := Uo) R)
    (shG_wm c φ φ₁ R dm) r
  refine h0.trans ?_
  rw [hr, map_mul, map_pow]

end ChartS1

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L1b =====
section

/-!
# S4-EtPBC-A, L1b (MVr): Mayer-Vietoris for free sheaves with arbitrary fibres of `Z`

**`mvC_shortExactR`**: the MV complex `Λ[W'] ⟶ Λ[W] ⊞ Λ[U] ⟶ Λ[Z]` of a commutative square `p₁ ≫ w = p₂ ≫ v` of
`P.Etale` is short exact when, at every geometric point `x` and every point `c` of the fibre of `Z` at `x`, the fibre
square satisfies `MVG1` (one point of `W` over `c`, `p₂` bijective over `c`) or `MVG2` (one point of `U` over `c`,
`p₁` bijective over `c`). Proof: stalks are free on fibres (`freeLin`), then `mv_inj`, `mv_surj`, `mv_exact` (L1a).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.GenAlg
  RamanujanPetersson.EtPBC.FreeStk

universe u

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}

/-- **Mayer-Vietoris for free sheaves, arbitrary `Z`**: short exact when every point of every geometric fibre of
`Z` satisfies `MVG1` or `MVG2` for the fibre square. -/
theorem mvC_shortExactR {W' W U Z : P.Etale} (p₁ : W' ⟶ W) (p₂ : W' ⟶ U) (w : W ⟶ Z) (v : U ⟶ Z)
    (hsq : p₁ ≫ w = p₂ ≫ v)
    (hgood : ∀ (x : P) (c : (geomPtAt x).point.fiber.obj Z),
      MVG1 ((geomPtAt x).point.fiber.map p₂) ((geomPtAt x).point.fiber.map w)
          ((geomPtAt x).point.fiber.map v) c ∨
        MVG2 ((geomPtAt x).point.fiber.map p₁) ((geomPtAt x).point.fiber.map w)
          ((geomPtAt x).point.fiber.map v) c) :
    (mvC Λ p₁ p₂ w v hsq).ShortExact := by
  have hmono : Mono (mvC Λ p₁ p₂ w v hsq).f := by
    rw [mono_iff_stalk]
    intro x
    rw [ModuleCat.mono_iff_injective, injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨l, rfl⟩ := freeLin_surjective (Λ := Λ) W' x z
    have h1 := congrArg (((geomPtAt x).stalkF Λ).map biprod.fst).hom hz
    have h2 := congrArg (((geomPtAt x).stalkF Λ).map biprod.snd).hom hz
    rw [stalk_comp_apply, biprod.lift_fst, freeLin_natural, map_zero] at h1
    rw [stalk_comp_apply, biprod.lift_snd, Functor.map_neg, ModuleCat.hom_neg, LinearMap.neg_apply,
      freeLin_natural, map_zero, neg_eq_zero] at h2
    have hl := mv_inj _ _ _ _ (fiber_sq hsq x) (hgood x) l
      (freeLin_injective W x (h1.trans (map_zero (freeLin Λ W x)).symm))
      (freeLin_injective U x (h2.trans (map_zero (freeLin Λ U x)).symm))
    rw [hl, map_zero]
  have hepi : Epi (mvC Λ p₁ p₂ w v hsq).g := by
    rw [epi_iff_stalk]
    intro x
    rw [ModuleCat.epi_iff_surjective]
    intro z
    obtain ⟨r, rfl⟩ := freeLin_surjective (Λ := Λ) Z x z
    obtain ⟨p, q, hpq⟩ := mv_surj _ _ _ _ (hgood x) r
    refine ⟨(((geomPtAt x).stalkF Λ).map biprod.inl).hom (freeLin Λ W x p) +
      (((geomPtAt x).stalkF Λ).map biprod.inr).hom (freeLin Λ U x q), ?_⟩
    rw [map_add, stalk_comp_apply, biprod.inl_desc, stalk_comp_apply, biprod.inr_desc, freeLin_natural,
      freeLin_natural, ← map_add, hpq]
  refine ShortComplex.ShortExact.mk' ?_ hmono hepi
  rw [exact_iff_stalk]
  intro x
  rw [ShortComplex.moduleCat_exact_iff]
  intro y hy
  obtain ⟨p, hp⟩ := freeLin_surjective W x ((((geomPtAt x).stalkF Λ).map biprod.fst).hom y)
  obtain ⟨q, hq⟩ := freeLin_surjective U x ((((geomPtAt x).stalkF Λ).map biprod.snd).hom y)
  have hR : (((geomPtAt x).stalkF Λ).map (biprod.desc (freeMap Λ w) (freeMap Λ v))).hom y =
      freeLin Λ Z x (Finsupp.mapDomain ((geomPtAt x).point.fiber.map w) p +
        Finsupp.mapDomain ((geomPtAt x).point.fiber.map v) q) := by
    have e1 : ∀ a, (((geomPtAt x).stalkF Λ).map (biprod.desc (freeMap Λ w) (freeMap Λ v))).hom
        ((((geomPtAt x).stalkF Λ).map biprod.inl).hom a) = (((geomPtAt x).stalkF Λ).map (freeMap Λ w)).hom a :=
      fun a => by rw [stalk_comp_apply, biprod.inl_desc]
    have e2 : ∀ a, (((geomPtAt x).stalkF Λ).map (biprod.desc (freeMap Λ w) (freeMap Λ v))).hom
        ((((geomPtAt x).stalkF Λ).map biprod.inr).hom a) = (((geomPtAt x).stalkF Λ).map (freeMap Λ v)).hom a :=
      fun a => by rw [stalk_comp_apply, biprod.inr_desc]
    conv_lhs => rw [stalk_biprod_eq x y]
    rw [map_add, e1, e2, ← hp, ← hq, freeLin_natural, freeLin_natural, map_add]
  have hy' : (((geomPtAt x).stalkF Λ).map (biprod.desc (freeMap Λ w) (freeMap Λ v))).hom y = 0 := hy
  rw [hR] at hy'
  have hpq := freeLin_injective Z x (hy'.trans (map_zero (freeLin Λ Z x)).symm)
  obtain ⟨l, hl1, hl2⟩ := mv_exact _ _ _ _ (fiber_sq hsq x) (hgood x) p q hpq
  refine ⟨freeLin Λ W' x l, ?_⟩
  show (((geomPtAt x).stalkF Λ).map (biprod.lift (freeMap Λ p₁) (-freeMap Λ p₂))).hom (freeLin Λ W' x l) = y
  refine stalk_biprod_ext x ?_ ?_
  · rw [stalk_comp_apply, biprod.lift_fst, freeLin_natural, hl1, hp]
  · rw [stalk_comp_apply, biprod.lift_snd, Functor.map_neg, ModuleCat.hom_neg, LinearMap.neg_apply,
      freeLin_natural, hl2, map_neg, hq, neg_neg]

end RamanujanPetersson.EtPBC.EtMV

end

end


