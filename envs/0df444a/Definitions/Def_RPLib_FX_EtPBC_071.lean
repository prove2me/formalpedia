-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_071
-- name    : RPLib_FX_EtPBC_071
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:39:23.6788+00:00
-- url     : https://prove2.me/theorems/70dbfa71-0c4f-54df-b4b6-da513a0b9588
-- title:
--   Proper base change for the projective line, library file 071
-- statement:
--   File 071 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovL3`: S4-EtPBC-A, R4-T2 (A1c): the tower of nilpotent lifts of a two-chart etale cover
--   * `S4.Def_RP_EtPBC_A_CovG2`: S4-EtPBC-A, R4-T2 (A2b): Serre vanishing modulo an ideal, uniformly along transitions
--   * `S4.Def_RP_EtPBC_A_CovHat2`: S4-EtPBC-A, R4-T2 (A2c-3b): the completed overlap ring and the maps from the base charts
--   * `S4.Def_RP_EtPBC_A_CovPr14`: S4-EtPBC-A, R4-T2 (A3n): the residue of a descended presentation on tensor charts
--   * `S4.Def_RP_EtPBC_A_Z2Lift`: S4-EtPBC-A, (Z2d): idempotents on the two charts lift to approximate global idempotents
--   * `S4.Def_RP_EtPBC_A_Z2Pi0`: S4-EtPBC-A, (Z): idempotents of the fibre of a finite cover of `P¹_A` spread out to an etale neighbourhood
--   * `S4.Def_RP_EtPBC_A_Z4Base`: S4-EtPBC-A, (Z) geometric layer 10 (G-e, part 2): the idempotent on `Y ×_V Spec R'`
--   * `S4.Def_RP_EtPBC_A_Z4FibB`: S4-EtPBC-A, (Z) geometric layer 12 (G-f, part 2): residue maps and the comparison map `Y_x ⟶ Y_{V'}`
--   * `S4.Def_RP_EtPBC_A_CovY`: S4-EtPBC-A, R4-T2 (G1b): affine charts of `Y_{V'} = Y ×_V Spec R'`
--   * `S4.Def_RP_EtPBC_A_CovCv`: S4-EtPBC-A, R4-T2 (G1c, part 1): the locally directed chart cover of `Y_{V'}`
--   * `S4.Def_RP_EtPBC_A_CovFbC`: S4-EtPBC-A, R4-T2 (G1d, part 3): the chart identity and the pullback square of the fibre cover
--   * `S4.Def_RP_EtPBC_A_CovFib`: S4-EtPBC-A, R4-T2 (G1d): the lifted cover restricts to the given fibre cover
--   * `S4.Def_RP_EtPBC_A_VPart`: S4-EtPBC-A, M2 F7/F9a: the value function on points, and base change from a section with the same values
--   * `S4.Def_RP_EtPBC_A_FBCv`: S4-EtPBC-A, R4 (FBC-c, part 1): sections of a constant sheaf with prescribed values on a finite fibre
--   * `S4.Def_RP_EtPBC_A_O2P2`: S4-EtPBC-A, O2 M5 P2: purity for Kummer characters (group level)
--   * `S4.Def_RP_EtPBC_A_O2Gl2d`: S4-EtPBC-A, O2 GLOB (O2Gl2d): stage S4, the global unit `H` seen on `W₂`
--   * `S4.Def_RP_EtPBC_A_O2Bd4`: S4-EtPBC-A, O2 REL (O2Bd4): bad-point data with NO chart map to `D_{g₀}`; `exists_S4H'`
--   * `S4.Def_RP_EtPBC_A_O2LocU`: S4-EtPBC-A, O2 GLOB (O2LocU): changing the open of a one-point MV class
--   * `S4.Def_RP_EtPBC_A_O2PP5a`: S4-EtPBC-A, O2 PP' (O2PP5a): an `IsLoc` class at `c(a)` comes from a domain chart over a fixed cofinite `U₀`
--   * `S4.Def_RP_EtPBC_A_O2L5c1`: S4-EtPBC-A, L5c1 (Geo3): the Mayer-Vietoris square of the graph-open `D̃` on `P¹_S`
--   * `S4.Def_RP_EtPBC_A_O2L5c2`: S4-EtPBC-A, L5c2: the family point class `αZ` on `P¹_S` at a chart point
--   * `S4.Def_RP_EtPBC_A_O2L6b1`: S4-EtPBC-A, L6b1: the `K`-rational fibre `ι' : P¹_K ⟶ P¹_S` and the horizontal section `σ'` of `ι'^* Zz`
--   * `S4.Def_RP_EtPBC_A_O2L6b2`: S4-EtPBC-A, L6b2: the `D` side of the comparison on `P¹_K`
--   * `S4.Def_RP_EtPBC_A_O2L6b3`: S4-EtPBC-A, L6b3: the morphism of MV data `locC(D♭) ⟶ ιP^* MVZ` on `P¹_K`
--   * `S4.Def_RP_EtPBC_A_O2L6c1`: S4-EtPBC-A, L6c1: a point class on `P¹_K` through the family square
--   * `S4.Def_RP_EtPBC_A_O2L7b1`: S4-EtPBC-A, O2 L7b1: the transport `Tr` from `P¹_K` to the fibre `P_s`
--   * `S4.Def_RP_EtPBC_A_O2L7b2`: S4-EtPBC-A, O2 L7b2: transport of family MV-theta classes
--   * `S4.Def_RP_EtPBC_A_O2L7c1`: S4-EtPBC-A, O2 L7c1: the transport `TrE` as an additive map; point classes transport into germs
--   * `S4.Def_RP_EtPBC_A_O2L8a`: S4-EtPBC-A, O2 L8a: finite coproducts, and the transport `TrG` for every sheaf on `P¹_S`
--   * `S4.Def_RP_EtPBC_A_O2L8b`: S4-EtPBC-A, O2 L8b: `TrG` is onto and natural; `BCSurj 2` for `FGT` sheaves; killing degree-1 classes
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_053
import Definitions.Def_RPLib_FX_EtPBC_062

/-!
# Proper base change for the projective line, library file 071

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovL3`: S4-EtPBC-A, R4-T2 (A1c): the tower of nilpotent lifts of a two-chart etale cover
* `S4.Def_RP_EtPBC_A_CovG2`: S4-EtPBC-A, R4-T2 (A2b): Serre vanishing modulo an ideal, uniformly along transitions
* `S4.Def_RP_EtPBC_A_CovHat2`: S4-EtPBC-A, R4-T2 (A2c-3b): the completed overlap ring and the maps from the base charts
* `S4.Def_RP_EtPBC_A_CovPr14`: S4-EtPBC-A, R4-T2 (A3n): the residue of a descended presentation on tensor charts
* `S4.Def_RP_EtPBC_A_Z2Lift`: S4-EtPBC-A, (Z2d): idempotents on the two charts lift to approximate global idempotents
* `S4.Def_RP_EtPBC_A_Z2Pi0`: S4-EtPBC-A, (Z): idempotents of the fibre of a finite cover of `P¹_A` spread out to an etale neighbourhood
* `S4.Def_RP_EtPBC_A_Z4Base`: S4-EtPBC-A, (Z) geometric layer 10 (G-e, part 2): the idempotent on `Y ×_V Spec R'`
* `S4.Def_RP_EtPBC_A_Z4FibB`: S4-EtPBC-A, (Z) geometric layer 12 (G-f, part 2): residue maps and the comparison map `Y_x ⟶ Y_{V'}`
* `S4.Def_RP_EtPBC_A_CovY`: S4-EtPBC-A, R4-T2 (G1b): affine charts of `Y_{V'} = Y ×_V Spec R'`
* `S4.Def_RP_EtPBC_A_CovCv`: S4-EtPBC-A, R4-T2 (G1c, part 1): the locally directed chart cover of `Y_{V'}`
* `S4.Def_RP_EtPBC_A_CovFbC`: S4-EtPBC-A, R4-T2 (G1d, part 3): the chart identity and the pullback square of the fibre cover
* `S4.Def_RP_EtPBC_A_CovFib`: S4-EtPBC-A, R4-T2 (G1d): the lifted cover restricts to the given fibre cover
* `S4.Def_RP_EtPBC_A_VPart`: S4-EtPBC-A, M2 F7/F9a: the value function on points, and base change from a section with the same values
* `S4.Def_RP_EtPBC_A_FBCv`: S4-EtPBC-A, R4 (FBC-c, part 1): sections of a constant sheaf with prescribed values on a finite fibre
* `S4.Def_RP_EtPBC_A_O2P2`: S4-EtPBC-A, O2 M5 P2: purity for Kummer characters (group level)
* `S4.Def_RP_EtPBC_A_O2Gl2d`: S4-EtPBC-A, O2 GLOB (O2Gl2d): stage S4, the global unit `H` seen on `W₂`
* `S4.Def_RP_EtPBC_A_O2Bd4`: S4-EtPBC-A, O2 REL (O2Bd4): bad-point data with NO chart map to `D_{g₀}`; `exists_S4H'`
* `S4.Def_RP_EtPBC_A_O2LocU`: S4-EtPBC-A, O2 GLOB (O2LocU): changing the open of a one-point MV class
* `S4.Def_RP_EtPBC_A_O2PP5a`: S4-EtPBC-A, O2 PP' (O2PP5a): an `IsLoc` class at `c(a)` comes from a domain chart over a fixed cofinite `U₀`
* `S4.Def_RP_EtPBC_A_O2L5c1`: S4-EtPBC-A, L5c1 (Geo3): the Mayer-Vietoris square of the graph-open `D̃` on `P¹_S`
* `S4.Def_RP_EtPBC_A_O2L5c2`: S4-EtPBC-A, L5c2: the family point class `αZ` on `P¹_S` at a chart point
* `S4.Def_RP_EtPBC_A_O2L6b1`: S4-EtPBC-A, L6b1: the `K`-rational fibre `ι' : P¹_K ⟶ P¹_S` and the horizontal section `σ'` of `ι'^* Zz`
* `S4.Def_RP_EtPBC_A_O2L6b2`: S4-EtPBC-A, L6b2: the `D` side of the comparison on `P¹_K`
* `S4.Def_RP_EtPBC_A_O2L6b3`: S4-EtPBC-A, L6b3: the morphism of MV data `locC(D♭) ⟶ ιP^* MVZ` on `P¹_K`
* `S4.Def_RP_EtPBC_A_O2L6c1`: S4-EtPBC-A, L6c1: a point class on `P¹_K` through the family square
* `S4.Def_RP_EtPBC_A_O2L7b1`: S4-EtPBC-A, O2 L7b1: the transport `Tr` from `P¹_K` to the fibre `P_s`
* `S4.Def_RP_EtPBC_A_O2L7b2`: S4-EtPBC-A, O2 L7b2: transport of family MV-theta classes
* `S4.Def_RP_EtPBC_A_O2L7c1`: S4-EtPBC-A, O2 L7c1: the transport `TrE` as an additive map; point classes transport into germs
* `S4.Def_RP_EtPBC_A_O2L8a`: S4-EtPBC-A, O2 L8a: finite coproducts, and the transport `TrG` for every sheaf on `P¹_S`
* `S4.Def_RP_EtPBC_A_O2L8b`: S4-EtPBC-A, O2 L8b: `TrG` is onto and natural; `BCSurj 2` for `FGT` sheaves; killing degree-1 classes
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_CovL3 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A1c): the tower of nilpotent lifts of a two-chart etale cover

* **`TwoCov φb₀ φb₁ τ₀ τ₁`**: a two-chart finite etale cover (bundled rings, `RingHom.Etale`/`Finite` properties);
  **`TwoCovHom π₀ π₁ π C' C`**: a transition `C' → C` over reductions `πᵢ`, `π` (surjective, kernels, squares);
* **`exists_lift`**: `lift_step` in this language;
* levels `B ⧸ J^(k+1)`: `down` (square-zero kernel), `qmap` (with `isAwayMap_qmap`, `isUnit_qmap`, `qmap_down`);
* **`tower`**, **`towerHom`**: the lifts of a level-0 cover to all levels `k`, with transitions.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Cov

end Cov

section Hom

end Hom

section Lift

variable {B₀ B₁ N b₀ b₁ n : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing b₀] [CommRing b₁]
  [CommRing n]

/-- **One lifting step** (`lift_step`) for bundled two-chart covers. -/
theorem exists_lift (φ₀ : B₀ →+* N) (φ₁ : B₁ →+* N) (t₀ : B₀) (t₁ : B₁) (hφ₀ : IsAwayMap φ₀ t₀)
    (hφ₁ : IsAwayMap φ₁ t₁) (hu₀ : IsUnit (φ₀ t₀)) (hu₁ : IsUnit (φ₁ t₁))
    (π₀ : B₀ →+* b₀) (π₁ : B₁ →+* b₁) (π : N →+* n) (hπ₀ : Function.Surjective π₀)
    (hπ₁ : Function.Surjective π₁) (hk₀ : IsNilpotent (RingHom.ker π₀)) (hk₁ : IsNilpotent (RingHom.ker π₁))
    (φb₀ : b₀ →+* n) (φb₁ : b₁ →+* n) (hc₀ : φb₀.comp π₀ = π.comp φ₀) (hc₁ : φb₁.comp π₁ = π.comp φ₁)
    (C : TwoCov φb₀ φb₁ (π₀ t₀) (π₁ t₁)) :
    Nonempty (Σ C' : TwoCov φ₀ φ₁ t₀ t₁, TwoCovHom π₀ π₁ π C' C) := by
  letI := C.a₀.toAlgebra
  letI := C.a₁.toAlgebra
  letI := C.a.toAlgebra
  haveI : Algebra.Etale b₀ C.E₀ := RingHom.etale_algebraMap.1 C.et₀
  haveI : Algebra.Etale b₁ C.E₁ := RingHom.etale_algebraMap.1 C.et₁
  obtain ⟨E₀, E₁, E, _, _, _, _, _, _, het₀, het₁, _, ρ₀, ρ₁, ρ, ψ₀, ψ₁, hs₀, hs₁, hs, hk₀', hk₁', hk',
    hc₀', hc₁', hc', hψ₀, hψ₁, aw₀, aw₁, hd₀, hd₁, hf₀, hf₁⟩ :=
    lift_step φ₀ φ₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ π₀ π₁ π hπ₀ hπ₁ hk₀ hk₁ φb₀ φb₁ hc₀ hc₁ C.E₀ C.E₁ C.E C.ψ₀ C.ψ₁
      C.hψ₀ C.hψ₁ C.aw₀ C.aw₁
  exact ⟨⟨⟨CommRingCat.of E₀, CommRingCat.of E₁, CommRingCat.of E, algebraMap B₀ E₀, algebraMap B₁ E₁,
    algebraMap N E, RingHom.etale_algebraMap.2 het₀, RingHom.etale_algebraMap.2 het₁,
    RingHom.finite_algebraMap.2 (hf₀ C.fin₀), RingHom.finite_algebraMap.2 (hf₁ C.fin₁), ψ₀, ψ₁, hψ₀, hψ₁, aw₀,
    aw₁⟩, ⟨ρ₀, ρ₁, ρ, hs₀, hs₁, hs, hk₀', hk₁', hk', hc₀', hc₁', hc', hd₀, hd₁⟩⟩⟩

end Lift

section Lvl

end Lvl

section Tower

end Tower

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovG2 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2b): Serre vanishing modulo an ideal, uniformly along transitions

For a two-chart cover `C` with ring maps `ιᵢ : R → Eᵢ` (agreeing on the overlap) and an ideal `I` of the overlap:
* **`TwoCov.Good C ι₀ I m y e`**: `E₀` is generated over `R[t]` by `m` modulo `ψ₀⁻¹ I`, and `ψ₀ mᵢ ≡ u^{eᵢ} ψ₁ yᵢ`
  modulo `I` (transition exponents `eᵢ`);
* **`TwoCov.h1_mod`**: then `H¹(O(d)) = 0` modulo `I` for `d ≥ max eᵢ`;
* **`TwoCov.good_zero`**: `Good` holds (any `I`, `I = ⊥` included) when `E₀` is finite over `R[t]`;
* **`TwoCovHom.good_lift`**: `Good` lifts along a transition with the SAME exponents (so `d` is uniform);
* **`TwoCovHom.hker_of_h1`**, **`TwoCovHom.secMap_surj_of_h1`**: `H¹ = 0` modulo `I'` and a kernel generated by
  `q` with `q · I' = 0` give the kernel hypothesis of `secMap_surj`: sections lift.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Good

end Good

section Zero

end Zero

section Lift

end Lift

section Ker

variable {B₀ B₁ N b₀ b₁ n : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing b₀] [CommRing b₁]
  [CommRing n] {φ₀ : B₀ →+* N} {φ₁ : B₁ →+* N} {t₀ : B₀} {t₁ : B₁} {φb₀ : b₀ →+* n} {φb₁ : b₁ →+* n} {τ₀ : b₀}
  {τ₁ : b₁} {π₀ : B₀ →+* b₀} {π₁ : B₁ →+* b₁} {π : N →+* n} {C' : TwoCov φ₀ φ₁ t₀ t₁}
  {C : TwoCov φb₀ φb₁ τ₀ τ₁} (H : TwoCovHom π₀ π₁ π C' C) {R : Type u} [CommRing R]
  (ι₀' : R →+* C'.E₀) (ι₁' : R →+* C'.E₁) (hι' : C'.ψ₀.comp ι₀' = C'.ψ₁.comp ι₁') (q : Ideal R)
  (hq₀ : ∀ α ∈ q, H.ρ₀ (ι₀' α) = 0) (hq₁ : ∀ α ∈ q, H.ρ₁ (ι₁' α) = 0)
  (hkρ : RingHom.ker H.ρ ≤ q.map (C'.ψ₀.comp ι₀')) (I' : Ideal C'.E)
  (hqI : ∀ α ∈ q, ∀ i ∈ I', C'.ψ₀ (ι₀' α) * i = 0) (d : ℕ)
  (h1 : ∀ z : C'.E, ∃ (x₀ : C'.E₀) (x₁ : C'.E₁), z - (C'.ψ₀ x₀ - C'.u ^ d * C'.ψ₁ x₁) ∈ I')

include hι' hq₀ hq₁ hkρ hqI h1

/-- **Sections lift** along a transition whose kernel is generated by `q`, when `H¹ = 0` modulo `I'`. -/
theorem TwoCovHom.secMap_surj_of_h1 (hτ₀ : π₀ t₀ = τ₀) : Function.Surjective (H.secMap hτ₀ d) :=
  H.secMap_surj hτ₀ d (H.hker_of_h1 ι₀' ι₁' hι' q hq₀ hq₁ hkρ I' hqI d h1)

end Ker

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

theorem liftN₁_inv (hts : φ₀ t₀ * φ₁ t₁ = 1) (hφ₁ : IsAwayMap φ₁ t₁) (hu₁ : IsUnit (φ₁ t₁)) :
    jL₁ C (sFm C) * liftN₁ C hφ₁ hu₁ (φ₀ t₀) = 1 := by
  rw [← liftN₁_φ₁ C hφ₁ hu₁ t₁, ← map_mul, mul_comm, hts, map_one]

end Hat2

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovPr14 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3n): the residue of a descended presentation on tensor charts

With `fh = σh ⊗ id : C ⊗ B → Ah ⊗ B`, `f' = σ ⊗ id : C ⊗ B → R' ⊗ B`, `θh : Pres (gmap fh gC) → Q` restricting to
`kap res` on `Ah ⊗ B`:
* `exists_cov`, **`hκT`** (the compatibility needed by `resid`), `lamT` (`lamT_apply`, `lamT_hlam`);
* **`resid_surj_T`**, **`resid_ker_T`**: the residue `resid fh f' gC θh (kap χ') _` is onto with kernel
  `Jt B χ' · Pres (gmap f' gC)`, when `ker θh = pI · Pres` with `pI ≤ ker res`.
-/

set_option autoImplicit false

open TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

variable {K A R' B Ah C Q : Type u} [Field K] [CommRing A] [CommRing R'] [Algebra A R'] [CommRing B] [Algebra A B]
  [CommRing Ah] [Algebra A Ah] [CommRing C] [Algebra A C] [CommRing Q]
  (χ : A →+* K) (χ' : R' →+* K) (res : Ah →+* K)
  (hres : ∀ a, res (algebraMap A Ah a) = χ a) (hχ' : ∀ a, χ' (algebraMap A R' a) = χ a)
  (ν : K →+* Q) (βQ : B →+* Q) (hβ : ∀ a, βQ (algebraMap A B a) = ν (χ a))

variable {r : ℕ} (σh : C →ₐ[A] Ah) (σ : C →ₐ[A] R') (gC : Fin r → MvPolynomial (Fin r) (C ⊗[A] B))
  (θh : Pres (gmap (Algebra.TensorProduct.map σh (AlgHom.id A B)).toRingHom gC) →+* Q)

theorem lamT_hlam (s : K →+* R') (hs : ∀ k, χ' (s k) = k) (hσ : ∀ c, χ' (σ c) = res (σh c)) (c : C ⊗[A] B) :
    lamT χ χ' res hres hχ' σ gC s hs (Algebra.TensorProduct.map σh (AlgHom.id A B) c) =
      presMap (Ideal.Quotient.mk (Jt B χ')) (gmap (Algebra.TensorProduct.map σ (AlgHom.id A B)).toRingHom gC)
        (algebraMap (R' ⊗[A] B) (Pres (gmap (Algebra.TensorProduct.map σ (AlgHom.id A B)).toRingHom gC))
          (Algebra.TensorProduct.map σ (AlgHom.id A B) c)) :=
  (congrArg (algebraMap ((R' ⊗[A] B) ⧸ Jt B χ')
    (Pres (gmap (Ideal.Quotient.mk (Jt B χ')) (gmap (Algebra.TensorProduct.map σ (AlgHom.id A B)).toRingHom gC)))) (lamQ_map χ χ' res s hres hχ' hs σh σ hσ c)).trans
    (presMap_algebraMap _ _ _).symm

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_Z2Lift =====
section

/-!
# S4-EtPBC-A, (Z2d): idempotents on the two charts lift to approximate global idempotents

`A` noetherian, `I ⊆ A`, chart algebras `B₀` (over `A[t]`), `B₁` (over `A[s]`, both written over `A[X]`) and the
overlap algebra `N`, with `φ₀ : B₀ →ₐ[A[X]] N`, `φ₁ : B₁ →ₐ[A] N`, `X • φ₁ (X • m) = φ₁ m`.

* `idem_lift`: an idempotent mod `K` lifts to an idempotent mod `K^m` (nilpotent kernel, Mathlib 00J9 form).
* `idem_unique`: idempotents mod `L^m` congruent mod `L` are congruent mod `L^m`.
* `mem_smul_top_pow`: `x ∈ I^k • ⊤ ↔ x ∈ (I B)^k`.
* **`idem_twoChart`**: a pair of idempotents mod `I` on the two charts agreeing mod `I` on the overlap is congruent
  mod `I` to a pair `(a, b)` with `φ₀ a = φ₁ b` (a global section) that is idempotent mod `I^(n+1)`, for any `n`.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Z2

open RamanujanPetersson.EtPBC.Z1

universe u v w w'

variable {A : Type u} [CommRing A]

section Idem

end Idem

section TwoChart

variable {B₀ : Type v} {B₁ : Type w} {N : Type w'}
  [CommRing B₀] [Algebra A[X] B₀] [Algebra A B₀] [IsScalarTower A A[X] B₀]
  [CommRing B₁] [Algebra A[X] B₁] [Algebra A B₁] [IsScalarTower A A[X] B₁]
  [CommRing N] [Algebra A[X] N] [Algebra A N] [IsScalarTower A A[X] N]

/-- **Approximate global idempotents**: chart idempotents mod `I` agreeing mod `I` on the overlap are congruent mod
`I` to a global section `(a, b)` (`φ₀ a = φ₁ b`) that is idempotent mod `I^(n+1)`. -/
theorem idem_twoChart [IsNoetherianRing A] [Module.Finite A[X] B₁] (I : Ideal A) (φ₀ : B₀ →ₐ[A[X]] N)
    (φ₁ : B₁ →ₐ[A] N) (h₁ : ∀ m, (X : A[X]) • φ₁ ((X : A[X]) • m) = φ₁ m)
    (hgen : ∀ m : B₁, ∃ (d : ℕ) (a : B₀), φ₀ a = (X ^ d : A[X]) • φ₁ m)
    (hloc : ∀ y : N, ∃ (k : ℕ) (b : B₁), y = (X ^ k : A[X]) • φ₁ b) :
    ∀ (n : ℕ) (a₀ : B₀) (b₀ : B₁), a₀ * a₀ - a₀ ∈ I.map (algebraMap A B₀) →
      b₀ * b₀ - b₀ ∈ I.map (algebraMap A B₁) → φ₀ a₀ - φ₁ b₀ ∈ I.map (algebraMap A N) →
      ∃ (a : B₀) (b : B₁), φ₀ a = φ₁ b ∧ a * a - a ∈ I.map (algebraMap A B₀) ^ (n + 1) ∧
        b * b - b ∈ I.map (algebraMap A B₁) ^ (n + 1) ∧ a - a₀ ∈ I.map (algebraMap A B₀) ∧
        b - b₀ ∈ I.map (algebraMap A B₁) := by
  obtain ⟨c, hc⟩ := lift_twoChart I φ₀.toLinearMap φ₁.toLinearMap h₁ hgen hloc
  intro n a₀ b₀ ha₀ hb₀ hab₀
  set K₀ := I.map (algebraMap A B₀) with hK₀
  set K₁ := I.map (algebraMap A B₁) with hK₁
  set L := I.map (algebraMap A N) with hL
  have hmap₀ : K₀.map (φ₀ : B₀ →+* N) = L := by
    rw [hK₀, hL, Ideal.map_map]
    exact congrArg (fun f => I.map f) (φ₀.restrictScalars A).comp_algebraMap
  have hmap₁ : K₁.map (φ₁ : B₁ →+* N) = L := by
    rw [hK₁, hL, Ideal.map_map]
    exact congrArg (fun f => I.map f) φ₁.comp_algebraMap
  have hφ₀ : ∀ (k : ℕ) (z : B₀), z ∈ K₀ ^ k → φ₀ z ∈ L ^ k := fun k z hz => by
    have := Ideal.mem_map_of_mem (φ₀ : B₀ →+* N) hz
    rwa [Ideal.map_pow, hmap₀] at this
  have hφ₁ : ∀ (k : ℕ) (z : B₁), z ∈ K₁ ^ k → φ₁ z ∈ L ^ k := fun k z hz => by
    have := Ideal.mem_map_of_mem (φ₁ : B₁ →+* N) hz
    rwa [Ideal.map_pow, hmap₁] at this
  obtain ⟨a₁, ha₁, ha₁₀⟩ := idem_lift K₀ (n + 1 + c) a₀ ha₀
  obtain ⟨b₁, hb₁, hb₁₀⟩ := idem_lift K₁ (n + 1 + c) b₀ hb₀
  have he : φ₀ a₁ * φ₀ a₁ - φ₀ a₁ ∈ L ^ (n + 1 + c) := by
    rw [← map_mul, ← map_sub]; exact hφ₀ _ _ ha₁
  have hf : φ₁ b₁ * φ₁ b₁ - φ₁ b₁ ∈ L ^ (n + 1 + c) := by
    rw [← map_mul, ← map_sub]; exact hφ₁ _ _ hb₁
  have hef : φ₀ a₁ - φ₁ b₁ ∈ L := by
    have h0 := hφ₀ 1 _ (by rw [pow_one]; exact ha₁₀)
    have h1 := hφ₁ 1 _ (by rw [pow_one]; exact hb₁₀)
    rw [pow_one, map_sub] at h0
    rw [pow_one, map_sub] at h1
    have : φ₀ a₁ - φ₁ b₁ = (φ₀ a₁ - φ₀ a₀) + (φ₀ a₀ - φ₁ b₀) - (φ₁ b₁ - φ₁ b₀) := by ring
    rw [this]
    exact L.sub_mem (L.add_mem h0 hab₀) h1
  have hN : φ₀ a₁ - φ₁ b₁ ∈ (I ^ (n + 1 + c) • ⊤ : Submodule A N) :=
    (mem_smul_top_pow I _ _).2 (idem_unique L _ he hf hef)
  obtain ⟨a', b', hab', ha', hb'⟩ := hc (n + 1) a₁ b₁ hN
  rw [mem_smul_top_pow] at ha' hb'
  have hle₀ : K₀ ^ (n + 1 + c) ≤ K₀ ^ (n + 1) := Ideal.pow_le_pow_right (Nat.le_add_right _ _)
  have hle₁ : K₁ ^ (n + 1 + c) ≤ K₁ ^ (n + 1) := Ideal.pow_le_pow_right (Nat.le_add_right _ _)
  refine ⟨a', b', hab', ?_, ?_, ?_, ?_⟩
  · have : a' * a' - a' = (a₁ * a₁ - a₁) + (a₁ - a') * ((a₁ - a') + 1 - 2 * a₁) := by ring
    rw [this]
    exact Ideal.add_mem _ (hle₀ ha₁) (Ideal.mul_mem_right _ _ ha')
  · have : b' * b' - b' = (b₁ * b₁ - b₁) + (b₁ - b') * ((b₁ - b') + 1 - 2 * b₁) := by ring
    rw [this]
    exact Ideal.add_mem _ (hle₁ hb₁) (Ideal.mul_mem_right _ _ hb')
  · have : a' - a₀ = (a₁ - a₀) - (a₁ - a') := by ring
    rw [this]
    exact K₀.sub_mem ha₁₀ (Ideal.pow_le_self (Nat.succ_ne_zero n) ha')
  · have : b' - b₀ = (b₁ - b₀) - (b₁ - b') := by ring
    rw [this]
    exact K₁.sub_mem hb₁₀ (Ideal.pow_le_self (Nat.succ_ne_zero n) hb')

end TwoChart

end RamanujanPetersson.EtPBC.Z2

end

end

-- ===== S4.Def_RP_EtPBC_A_Z2Pi0 =====
section

/-!
# S4-EtPBC-A, (Z): idempotents of the fibre of a finite cover of `P¹_A` spread out to an etale neighbourhood

Algebraic form of the `π₀` lemma: `A` noetherian, `p` prime, chart algebras `B₀` (over `A[t]`), `B₁` (over `A[s]`),
both finite over `A[X]`, overlap algebra `N`, `φ₀ : B₀ →ₐ[A[X]] N`, `φ₁ : B₁ →ₐ[A] N`.

* `secAlg φ₀ φ₁`: the global sections `{(a, b) | φ₀ a = φ₁ b}` as an `A`-subalgebra of `B₀ × B₁`;
  `secAlg_finite`: it is finite over `A` (Z1, `twoChart_fg`).
* `fibreMap p φ₀ φ₁ : secAlg →ₐ[A] κ(p) ⊗ B₀ × κ(p) ⊗ B₁` and `fibreUnit p B₀ B₁`.
* `includeRight_eq_of_sub_mem`: `x ≡ y mod p B` gives `1 ⊗ x = 1 ⊗ y` in `κ(p) ⊗ B`.
* **`exists_etale_idem_twoChart`**: chart elements `ε₀`, `ε₁` idempotent mod `p` and agreeing mod `p` on the overlap
  come, after an etale `A → A'` with a prime `P` over `p` and `κ(p) ≅ κ(P)`, from an idempotent of `A' ⊗ secAlg`.
-/

set_option autoImplicit false

open Polynomial
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Z2

open RamanujanPetersson.EtPBC.Z1

universe u v w w'

variable {A : Type u} [CommRing A]

section Fib

end Fib

section TwoChart

variable {B₀ : Type v} {B₁ : Type w} {N : Type w'}
  [CommRing B₀] [Algebra A[X] B₀] [Algebra A B₀] [IsScalarTower A A[X] B₀]
  [CommRing B₁] [Algebra A[X] B₁] [Algebra A B₁] [IsScalarTower A A[X] B₁]
  [CommRing N] [Algebra A[X] N] [Algebra A N] [IsScalarTower A A[X] N]

/-- **The global sections are finite over `A`.** -/
theorem secAlg_finite [IsNoetherianRing A] [Module.Finite A[X] B₀] [Module.Finite A[X] B₁]
    (φ₀ : B₀ →ₐ[A[X]] N) (φ₁ : B₁ →ₐ[A] N) (h₁ : ∀ m, (X : A[X]) • φ₁ ((X : A[X]) • m) = φ₁ m)
    (hgen : ∀ m : B₁, ∃ (d : ℕ) (a : B₀), φ₀ a = (X ^ d : A[X]) • φ₁ m)
    (hk₀ : ∀ a, φ₀ a = 0 → a ∈ xTors (A := A) B₀) (hk₁ : ∀ b, φ₁ b = 0 → b ∈ xTors (A := A) B₁) :
    Module.Finite A (secAlg φ₀ φ₁) := by
  have h := twoChart_fg φ₀.toLinearMap φ₁.toLinearMap h₁ hgen hk₀ hk₁
  rw [← secAlg_toSubmodule] at h
  exact Module.Finite.iff_fg.mpr h

end TwoChart

end RamanujanPetersson.EtPBC.Z2

end

end

-- ===== S4.Def_RP_EtPBC_A_Z4Base =====
section

/-!
# S4-EtPBC-A, (Z) geometric layer 10 (G-e, part 2): the idempotent on `Y ×_V Spec R'`

* `isoSpec_inv_appTop'`, `eq_Spec_map` (a morphism `Spec R ⟶ V`, `V` affine, is `Spec` of its ring map).
* `pushout_inl_surj`, `pushout_inl_ker`: in a pushout of commutative rings along a surjection `g : A ↠ C`, the map
  `inl : B → P` is surjective with kernel `(ker g) B`.
* `hV V R' : Spec R' ⟶ V`, `hV_appTop`; `YV K gV π R' = Y ×_V Spec R'` with its `Γ(V)`-algebra structure `algYV`;
  `fR : R' →ₐ Γ(Y_{V'}, ⊤)`, `gS : secAlg →ₐ Γ(Y_{V'}, ⊤)`, **`PhiY = lift fR gS`**; `isClopen_PhiY`: for an
  idempotent `e'` of `R' ⊗ secAlg`, `D(PhiY e')` is clopen.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open RamanujanPetersson.EtCompact
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Z3

universe u

section Base

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV) [IsAffine V] (R' : Type u) [CommRing R'] [Algebra Γ(V, ⊤) R']

attribute [local instance] algYV

/-- `secAlg → Γ(Y_{V'}, ⊤)` (glued section pulled back along the first projection). -/
def gS : Z2.secAlg (φY0 K gV π) (φY1 K gV π) →ₐ[Γ(V, ⊤)] Γ(YV K gV π R', ⊤) where
  toRingHom := (pullback.fst (π ≫ qV K gV) (hV V R')).appTop.hom.comp (glueRing K gV π)
  commutes' a := by
    change (pullback.fst (π ≫ qV K gV) (hV V R')).appTop.hom
      (glueRing K gV π (algebraMap Γ(V, ⊤) (Z2.secAlg (φY0 K gV π) (φY1 K gV π)) a)) = (strV K gV π R').hom a
    rw [glueRing_struct, strV, Scheme.Hom.comp_appTop]
    rfl

/-- **`R' ⊗_{Γ(V)} secAlg → Γ(Y ×_V Spec R', ⊤)`.** -/
def PhiY : R' ⊗[Γ(V, ⊤)] Z2.secAlg (φY0 K gV π) (φY1 K gV π) →ₐ[Γ(V, ⊤)] Γ(YV K gV π R', ⊤) :=
  Algebra.TensorProduct.lift (fR K gV π R') (gS K gV π R') (fun _ _ => Commute.all _ _)

theorem PhiY_tmul (r : R') (x : Z2.secAlg (φY0 K gV π) (φY1 K gV π)) :
    PhiY K gV π R' (r ⊗ₜ x) = fR K gV π R' r * gS K gV π R' x :=
  Algebra.TensorProduct.lift_tmul _ _ _ r x

/-- **`D(PhiY e')` is clopen** for an idempotent `e'`. -/
theorem isClopen_PhiY {e' : R' ⊗[Γ(V, ⊤)] Z2.secAlg (φY0 K gV π) (φY1 K gV π)} (he : IsIdempotentElem e') :
    IsClopen ((YV K gV π R').basicOpen (PhiY K gV π R' e') : Set (YV K gV π R')) :=
  isClopen_basicOpen (he.map (PhiY K gV π R'))

end Base

end RamanujanPetersson.EtPBC.Z3

end

end

-- ===== S4.Def_RP_EtPBC_A_Z4FibB =====
section

/-!
# S4-EtPBC-A, (Z) geometric layer 12 (G-f, part 2): residue maps and the comparison map `Y_x ⟶ Y_{V'}`

* `ψx K x : Γ(V) → K`, `px K x = ker ψx` (prime), `ker_appTop_eq`, `κx : κ(p) → K`, `κx_algebraMap`.
* For `P` over `p` with `κ(p) ≅ κ(P)` (`hbij`): `χx : R' → K`, `χx_algebraMap`, **`hxχ`**:
  `Spec χx ≫ hV V R' = x`, `xχ_appTop`.
* **`yxMap K gV π R' x x' hx' : Y_x ⟶ Y ×_V Spec R'`**, `yxMap_fR`, `yxMap_gS`, `yxMap_PhiY_tmul`.
* `exists_fibreRing`: a ring map `κ(p) ⊗ Γ(Y, U) → Γ(Y_x, fx⁻¹ U)`, `c ⊗ b ↦ c · fx^* b`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open RamanujanPetersson.EtCompact
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Z3

universe u

section Res

end Res

section Map

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN algYV

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV) [IsAffine V] (R' : Type u) [CommRing R'] [Algebra Γ(V, ⊤) R']
  (x : Spec (CommRingCat.of K) ⟶ V) (x' : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R'))
  (hx' : x' ≫ hV V R' = x)

theorem yxMap_gS (y : Z2.secAlg (φY0 K gV π) (φY1 K gV π)) :
    (yxMap K gV π R' x x' hx').appTop (gS K gV π R' y) = (fx K gV π x).appTop (glueRing K gV π y) := by
  have h := congrArg (fun φ => φ.appTop.hom (glueRing K gV π y))
    (pullback.lift_fst (fx K gV π x) (sx K gV π x ≫ x')
      (by rw [Category.assoc, hx']; exact pullback.condition))
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h
  exact h

theorem yxMap_PhiY_tmul (r : R') (y : Z2.secAlg (φY0 K gV π) (φY1 K gV π)) :
    (yxMap K gV π R' x x' hx').appTop (PhiY K gV π R' (r ⊗ₜ y)) =
      (sx K gV π x).appTop (x'.appTop ((Scheme.ΓSpecIso (CommRingCat.of R')).inv r)) *
        (fx K gV π x).appTop (glueRing K gV π y) := by
  rw [PhiY_tmul, map_mul, yxMap_fR, yxMap_gS]

end Map

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

/-- **The chart square is a pullback** of `hU.fromSpec` along `Y_{V'} ⟶ Y`. -/
theorem isPullback_chY : IsPullback (chY K gV π R' hU hA)
    (Spec.map (CommRingCat.ofHom (S := R' ⊗[Γ(V, ⊤)] Γ(Y, U)) Algebra.TensorProduct.includeRight.toRingHom))
    (pullback.fst (π ≫ qV K gV) (hV V R')) hU.fromSpec := by
  refine IsPullback.of_right ?_ (chY_fst K gV π R' hU hA) (IsPullback.of_hasPullback _ _).flip
  rw [chY_snd, fromSpec_str K gV π hU, ← hA]
  exact IsPullback.of_iso (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct Γ(V, ⊤) R' Γ(Y, U))) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (asIso V.isoSpec.inv) (by simp) (by simp) (by simp [hV]) (by simp)

end Chart

section Res

variable {U U' : Y.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (hle : U' ≤ U)
  [Algebra Γ(V, ⊤) Γ(Y, U)] [Algebra Γ(V, ⊤) Γ(Y, U')]
  (hA : CommRingCat.ofHom (algebraMap Γ(V, ⊤) Γ(Y, U)) = strU K gV π U)
  (hA' : CommRingCat.ofHom (algebraMap Γ(V, ⊤) Γ(Y, U')) = strU K gV π U')
  (φ : Γ(Y, U) →ₐ[Γ(V, ⊤)] Γ(Y, U')) (hφ : φ.toRingHom = (Y.presheaf.map (homOfLE hle).op).hom)

include hφ in
/-- **Charts are compatible with restriction.** -/
theorem chY_res : Spec.map (tmap R' φ) ≫ chY K gV π R' hU hA = chY K gV π R' hU' hA' := by
  have hres : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ hU.fromSpec = hU'.fromSpec := by
    rw [hφ]
    exact hU.map_fromSpec hU' (homOfLE hle).op
  have e1 : (Algebra.TensorProduct.map (AlgHom.id Γ(V, ⊤) R') φ).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := Γ(V, ⊤)) (A := R') (B := Γ(Y, U))).toRingHom =
      (Algebra.TensorProduct.includeRight (R := Γ(V, ⊤)) (A := R') (B := Γ(Y, U'))).toRingHom.comp
        φ.toRingHom := by
    ext b
    simp
  have e2 : (Algebra.TensorProduct.map (AlgHom.id Γ(V, ⊤) R') φ).toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom (R := Γ(V, ⊤)) (A := R') (B := Γ(Y, U))) =
      Algebra.TensorProduct.includeLeftRingHom (R := Γ(V, ⊤)) (A := R') (B := Γ(Y, U')) := by
    ext r
    simp
  apply pullback.hom_ext
  · rw [Category.assoc, chY_fst, chY_fst, ← hres, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e1]
  · rw [Category.assoc, chY_snd, chY_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e2]

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

/-- `φY0` over `Γ(V)`. -/
abbrev φ0V : Γ(Y, Yc K gV π 0) →ₐ[Γ(V, ⊤)] Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1) :=
  (φY0 K gV π).restrictScalars Γ(V, ⊤)

/-- The chart restriction `Spec (R' ⊗ Γ(Y₀₁)) ⟶ Spec (R' ⊗ Γ(Y₀))`. -/
abbrev a0 : Spec (CommRingCat.of (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1))) ⟶
    Spec (CommRingCat.of (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0))) :=
  Spec.map (tmap R' (φ0V K gV π))

/-- The chart restriction `Spec (R' ⊗ Γ(Y₀₁)) ⟶ Spec (R' ⊗ Γ(Y₁))`. -/
abbrev a1 : Spec (CommRingCat.of (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1))) ⟶
    Spec (CommRingCat.of (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 1))) :=
  Spec.map (tmap R' (φY1 K gV π))

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovFbC =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1d, part 3): the chart identity and the pullback square of the fibre cover

* `hxL_of`: a ring map `χ' : R' → K` over `x` gives a lift `Spec χ'` of `x`.
* **`fromSpec_yx`**: for a chart `U` of `Y` and `θ : E → Γ(T, q⁻¹ fx⁻¹ U)` as in `CoverLift`,
  `T_U ⟶ T ⟶ Y_x ⟶ Y_{V'}` equals `Spec θ ≫ Spec (alg) ≫ chY`.
* `mono_yxMap`: `Y_x ⟶ Y_{V'}` is a monomorphism.
* `pb_key`: the square of a chart of the pulled back gluing cover.
* `gW_congr`: `gW` only depends on `w`.
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
  (π : Y ⟶ PV K gV) (x : Spec (CommRingCat.of K) ⟶ V) [IsAffine V]

variable {R' : Type u} [CommRing R'] [Algebra Γ(V, ⊤) R'] (χ' : R' →+* K)
  (hxL : Spec.map (CommRingCat.ofHom χ') ≫ hV V R' = x)

section Chart

attribute [local instance] algKY algT

variable {T : Scheme.{u}} (q : T ⟶ Yx K gV π x)

/-- **The chart identity**: `T_U ⟶ T ⟶ Y_x ⟶ Y_{V'}` is `Spec θ ≫ Spec (alg) ≫ chY`. -/
theorem fromSpec_yx {U : Y.Opens} (hU : IsAffineOpen U) [Algebra Γ(V, ⊤) Γ(Y, U)]
    (hA : CommRingCat.ofHom (algebraMap Γ(V, ⊤) Γ(Y, U)) = strU K gV π U)
    (hW : IsAffineOpen (fx K gV π x ⁻¹ᵁ U)) (hT : IsAffineOpen (q ⁻¹ᵁ (fx K gV π x ⁻¹ᵁ U)))
    {E : Type u} [CommRing E] [Algebra (R' ⊗[Γ(V, ⊤)] Γ(Y, U)) E] (θ : E →+* Γ(T, q ⁻¹ᵁ (fx K gV π x ⁻¹ᵁ U)))
    (hθ : ∀ (r : R') (b : Γ(Y, U)), θ (algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, U)) E (r ⊗ₜ b)) =
      algebraMap Γ(Yx K gV π x, fx K gV π x ⁻¹ᵁ U) Γ(T, q ⁻¹ᵁ (fx K gV π x ⁻¹ᵁ U))
        (algebraMap K Γ(Yx K gV π x, fx K gV π x ⁻¹ᵁ U) (χ' r) * ((fx K gV π x).app U).hom b)) :
    hT.fromSpec ≫ q ≫ yxMap K gV π R' x _ hxL =
      Spec.map (CommRingCat.ofHom θ) ≫ Spec.map (CommRingCat.ofHom (algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, U)) E)) ≫
        chY K gV π R' hU hA := by
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [yxMap, pullback.lift_fst, chY_fst, ← IsAffineOpen.SpecMap_appLE_fromSpec_assoc q hW hT le_rfl,
      ← IsAffineOpen.SpecMap_appLE_fromSpec (fx K gV π x) hU hW le_rfl, ← Scheme.Hom.app_eq_appLE,
      ← Scheme.Hom.app_eq_appLE]
    simp only [← Spec.map_comp_assoc]
    refine congrArg (· ≫ hU.fromSpec) (congrArg Spec.map ?_)
    ext b
    show (q.app _).hom (((fx K gV π x).app U).hom b) = θ (algebraMap _ E ((1 : R') ⊗ₜ b))
    rw [hθ, map_one, map_one, one_mul] <;> rfl
  · simp only [Category.assoc]
    rw [yxMap, pullback.lift_snd, chY_snd, ← IsAffineOpen.SpecMap_appLE_fromSpec_assoc q hW hT le_rfl,
      ← IsAffineOpen.SpecMap_appLE_fromSpec_assoc (sx K gV π x) (isAffineOpen_top _) hW (by simp),
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Scheme.Hom.app_eq_appLE]
    simp only [← Spec.map_comp]
    refine congrArg Spec.map ?_
    ext r
    show (q.app _).hom (((sx K gV π x).appLE ⊤ _ _).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (χ' r))) =
      θ (algebraMap _ E (r ⊗ₜ (1 : Γ(Y, U))))
    rw [hθ, map_one, mul_one] <;> rfl

end Chart

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

theorem hxL : letI := algKV K gV; xL L ≫ hV V L.R' = x :=
  letI := algKV K gV; hxL_of K x L.χ' (fun a => L.hχ a)

/-- `Y_x ⟶ Y_{V'}`. -/
abbrev yxL : letI := algKV K gV; Yx K gV π x ⟶ YV K gV π L.R' :=
  letI := algKV K gV; yxMap K gV π L.R' x (xL L) (hxL L)

end RamanujanPetersson.EtPBC.Cov

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

/-- **`vv b` is locally constant.** -/
theorem isLocallyConstant_vv (b : unitSh Λ X ⟶ (pull ι Λ).obj ((push π Λ).obj (constSh Λ Y M))) :
    IsLocallyConstant (vv ι π b) := by
  refine (IsLocallyConstant.iff_exists_open _).2 fun q => ?_
  obtain ⟨N, hNo, hN, hc⟩ := vval_locConst₂ ι π b (geomPtAt q).pt
  have hq : (geomPtAt q).pt (default : Spec (CommRingCat.of (geomPtAt q).Ω)) = q := center_geomPtAt q
  refine ⟨N, hNo, hq ▸ hN, fun q' hq' => ?_⟩
  have hq'' : (geomPtAt q').pt (default : Spec (CommRingCat.of (geomPtAt q').Ω)) = q' := center_geomPtAt q'
  exact hc _ (geomPtAt q').pt (hq''.symm ▸ hq')

end Gen

section BC

end BC

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_FBCv =====
section

/-!
# S4-EtPBC-A, R4 (FBC-c, part 1): sections of a constant sheaf with prescribed values on a finite fibre

For `π : Y ⟶ P` finite, a geometric point `t` of `P`, a neighbourhood `j` of `t` and any `v : π⁻¹(j) → M`, after
refining `j` there is a section `z` of `M_Y` over `π⁻¹(j')` whose values along the fibre `fib π t` are those of `v`.
* `PhiU`: `R' ⊗_{Γ(W)} Γ(U) → Γ(U')` for a square `U' → U → W`, `U' → Spec R' → W`; `comap_PhiU_left/right`;
* `exists_sec_vals_aff` (affine `j`), **`exists_sec_vals`** (Stacks 00UL via
  `Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.FBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtPBC.Z3

universe u

section Phi

variable {W U U' : Scheme.{u}} [IsAffine W] (g : U ⟶ W) (R' : Type u) [CommRing R'] [Algebra Γ(W, ⊤) R']
  (f₁ : U' ⟶ Spec (CommRingCat.of R')) (f₂ : U' ⟶ U) [Algebra Γ(W, ⊤) Γ(U, ⊤)] [Algebra Γ(W, ⊤) Γ(U', ⊤)]

theorem PhiU_left (hg : algebraMap Γ(W, ⊤) Γ(U, ⊤) = g.appTop.hom)
    (h' : algebraMap Γ(W, ⊤) Γ(U', ⊤) = (f₁ ≫ hV W R').appTop.hom) (hf : f₂ ≫ g = f₁ ≫ hV W R') (r : R') :
    PhiU g R' f₁ f₂ hg h' hf (r ⊗ₜ 1) = f₁.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom r) := by
  show fRU R' f₁ h' r * gEU g R' f₁ f₂ hg h' hf 1 = _
  rw [map_one, mul_one]
  rfl

theorem PhiU_right (hg : algebraMap Γ(W, ⊤) Γ(U, ⊤) = g.appTop.hom)
    (h' : algebraMap Γ(W, ⊤) Γ(U', ⊤) = (f₁ ≫ hV W R').appTop.hom) (hf : f₂ ≫ g = f₁ ≫ hV W R')
    (s : Γ(U, ⊤)) : PhiU g R' f₁ f₂ hg h' hf (1 ⊗ₜ s) = f₂.appTop.hom s := by
  show fRU R' f₁ h' 1 * gEU g R' f₁ f₂ hg h' hf s = _
  rw [map_one, one_mul]
  rfl

theorem comap_PhiU_left (hg : algebraMap Γ(W, ⊤) Γ(U, ⊤) = g.appTop.hom)
    (h' : algebraMap Γ(W, ⊤) Γ(U', ⊤) = (f₁ ≫ hV W R').appTop.hom) (hf : f₂ ≫ g = f₁ ≫ hV W R') (u : U') :
    Ideal.comap (algebraMap R' (R' ⊗[Γ(W, ⊤)] Γ(U, ⊤)))
        (Ideal.comap (PhiU g R' f₁ f₂ hg h' hf) (PrimeSpectrum.asIdeal (U'.toSpecΓ u))) =
      PrimeSpectrum.asIdeal (f₁ u) := by
  rw [← toSpecΓ_Spec_asIdeal (CommRingCat.of R') (f₁ u), ← toSpecΓ_map_asIdeal f₁ u]
  ext r
  show PhiU g R' f₁ f₂ hg h' hf (r ⊗ₜ 1) ∈ PrimeSpectrum.asIdeal (U'.toSpecΓ u) ↔ _
  rw [PhiU_left]
  exact Iff.rfl

theorem comap_PhiU_right (hg : algebraMap Γ(W, ⊤) Γ(U, ⊤) = g.appTop.hom)
    (h' : algebraMap Γ(W, ⊤) Γ(U', ⊤) = (f₁ ≫ hV W R').appTop.hom) (hf : f₂ ≫ g = f₁ ≫ hV W R') (u : U') :
    Ideal.comap (Algebra.TensorProduct.includeRight : Γ(U, ⊤) →ₐ[Γ(W, ⊤)] R' ⊗[Γ(W, ⊤)] Γ(U, ⊤))
        (Ideal.comap (PhiU g R' f₁ f₂ hg h' hf) (PrimeSpectrum.asIdeal (U'.toSpecΓ u))) =
      PrimeSpectrum.asIdeal (U.toSpecΓ (f₂ u)) := by
  rw [← toSpecΓ_map_asIdeal f₂ u]
  ext s
  show PhiU g R' f₁ f₂ hg h' hf (1 ⊗ₜ s) ∈ PrimeSpectrum.asIdeal (U'.toSpecΓ u) ↔ _
  rw [PhiU_right]
  exact Iff.rfl

end Phi

section Main

end Main

end RamanujanPetersson.EtPBC.FBC

end

end

-- ===== S4.Def_RP_EtPBC_A_O2P2 =====
section

/-!
# S4-EtPBC-A, O2 M5 P2: purity for Kummer characters (group level)

* `exists_cdec`: a locally constant additive `χ : G → Λ` with finite image (`N • Λ = 0`) is
  `σ ↦ ∑ i, (c i σ).val • g i` with `c i : G → ZMod (d i)` additive locally constant, `d i ∣ N`, `d i • g i = 0`;
* `zvHom hg : ZMod d →+ Λ`, `a ↦ a.val • g` (`d • g = 0`), `zvHom_intCast`, `zvHom_apply`;
* `kchar_npow`, `kchar_inv`, `kchar_zpow`: `kchar (γ ^ m) = m * kchar γ`; `mem_rad_of_pow_eq`;
* `kumChi_twist`: `kumChi_d α g = kumChi_d (α τ^{(N/d) m}) g + kumChi_N τ ((-m) • g)`;
* `exists_tau`: an `N`-th root `τ` of `t` in `maxUnram Bt K`;
* **`cyc_twist`**: every locally constant additive `c : π₁(Bt) → ZMod d` gives `(c σ).val • g` as a Kummer character
  `kumChi_d α g` with `α ^ d = u ∈ K` having a `d`-th root in `maxUnram B K`, plus `kumChi_N τ ((-m) • g)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain

noncomputable section

namespace RamanujanPetersson.EtCompact.Pur

open RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer RamanujanPetersson.EtCompact.GalTrE

section Cdec

end Cdec

section Zv

end Zv

section KZ

end KZ

section Twist2

end Twist2

section Cyc

variable {B Bt K : Type} [CommRing B] [IsDedekindDomain B] [CommRing Bt] [IsDedekindDomain Bt] [Algebra B Bt]
  {t : B} [IsLocalization.Away t Bt]
  [Field K] [Algebra B K] [Algebra Bt K] [IsScalarTower B Bt K] [IsFractionRing B K] [IsFractionRing Bt K]

variable (ht : t ≠ 0) (hP : (Ideal.span {t}).IsPrime) {Λ : Type} [AddCommGroup Λ]

include ht hP in
/-- **Purity for a cyclic Kummer character** on `Bt = B[1/t]`. -/
theorem cyc_twist {N d : ℕ} [NeZero N] [NeZero d] (hN : IsUnit (N : B)) (hdN : d ∣ N)
    {ζ : maxUnram Bt K} (hζ : IsPrimitiveRoot ζ N) (hζd : IsPrimitiveRoot (ζ ^ (N / d)) d)
    (hζΓ : ∀ σ ∈ (⊤ : Subgroup (Pi1 Bt K)), σ ζ = ζ)
    {τ : (maxUnram Bt K)ˣ} (hτ : (τ : maxUnram Bt K) ^ N = algebraMap K (maxUnram Bt K) (algebraMap B K t))
    (c : Pi1 Bt K → ZMod d) (hc : IsLocallyConstant c) (hhom : ∀ σ τ, c (σ * τ) = c σ + c τ)
    {g : Λ} (hg : d • g = 0) :
    ∃ (α : (maxUnram Bt K)ˣ) (m : ℤ) (u : K), α ∈ rad (⊤ : Subgroup (Pi1 Bt K)) d ∧
      (α : maxUnram Bt K) ^ d = algebraMap K (maxUnram Bt K) u ∧
      (∃ γ : (maxUnram B K)ˣ, (γ : maxUnram B K) ^ d = algebraMap K (maxUnram B K) u) ∧
      ∀ σ, (c σ).val • g = kumChi hζd α g σ + kumChi hζ τ ((-m) • g) σ := by
  classical
  have hζdΓ : ∀ σ ∈ (⊤ : Subgroup (Pi1 Bt K)), σ (ζ ^ (N / d)) = ζ ^ (N / d) := fun σ hσ => by
    rw [map_pow, hζΓ σ hσ]
  obtain ⟨α0, hα0, hα0c⟩ := exists_kchar_eq hζd hζdΓ (fun σ : (⊤ : Subgroup (Pi1 Bt K)) => c σ)
    (hc.comp_continuous continuous_subtype_val) (fun σ τ => hhom σ τ)
  have hfix : ∀ σ : Pi1 Bt K, σ ((α0 : maxUnram Bt K) ^ d) = (α0 : maxUnram Bt K) ^ d :=
    fun σ => hα0 σ (Subgroup.mem_top σ)
  obtain ⟨u0, hu0'⟩ := (InfiniteGalois.mem_bot_iff_fixed (k := K) (K := maxUnram Bt K)
    ((α0 : maxUnram Bt K) ^ d)).2 hfix
  have hu0 : algebraMap K (maxUnram Bt K) u0 = (α0 : maxUnram Bt K) ^ d := hu0'
  have hu00 : u0 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hu0
    exact α0.ne_zero ((pow_eq_zero_iff (NeZero.ne d)).1 hu0.symm)
  have hd : IsUnit (d : B) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hdN) hN
  have hαAC : ((α0 : maxUnram Bt K) : AlgebraicClosure K) ^ d = algebraMap K (AlgebraicClosure K) u0 := by
    rw [← IntermediateField.coe_pow, ← hu0]
    rfl
  obtain ⟨m, hm⟩ := root_mem_maxUnram_twist ht hP hd (α0 : maxUnram Bt K).2 hu00 hαAC
  have htK : algebraMap B K t ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective B K)).2 ht
  have hu_ne : u0 * algebraMap B K t ^ m ≠ 0 := mul_ne_zero hu00 (zpow_ne_zero _ htK)
  obtain ⟨γ0, hγ0⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap K (AlgebraicClosure K) (u0 * algebraMap B K t ^ m)) (NeZero.pos d)
  let γ1 : maxUnram B K := ⟨γ0, hm γ0 hγ0⟩
  have hγ1 : γ1 ^ d = algebraMap K (maxUnram B K) (u0 * algebraMap B K t ^ m) :=
    Subtype.ext (by rw [IntermediateField.coe_pow]; exact hγ0)
  have hγ10 : γ1 ≠ 0 := by
    intro h
    rw [h, zero_pow (NeZero.ne d)] at hγ1
    exact hu_ne ((map_eq_zero_iff _ (algebraMap K (maxUnram B K)).injective).1 hγ1.symm)
  have hτN : ((τ ^ (N / d)) ^ m) ^ d = (τ ^ N) ^ m := by
    rw [← zpow_natCast ((τ ^ (N / d)) ^ m), ← zpow_mul, mul_comm m, zpow_mul, zpow_natCast, ← pow_mul,
      Nat.div_mul_cancel hdN]
  have hαd : ((α0 * (τ ^ (N / d)) ^ m : (maxUnram Bt K)ˣ) : maxUnram Bt K) ^ d =
      algebraMap K (maxUnram Bt K) (u0 * algebraMap B K t ^ m) := by
    rw [← Units.val_pow_eq_pow_val, mul_pow, hτN, Units.val_mul, Units.val_pow_eq_pow_val, ← hu0,
      Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, hτ, map_mul, map_zpow₀]
  refine ⟨α0 * (τ ^ (N / d)) ^ m, m, u0 * algebraMap B K t ^ m, mem_rad_of_pow_eq hαd, hαd,
    ⟨Units.mk0 γ1 hγ10, hγ1⟩, fun σ => ?_⟩
  have h1 : kumChi hζd α0 g σ = (c σ).val • g := by
    unfold kumChi
    rw [hα0c]
  rw [← h1]
  exact kumChi_twist hζ hζd hdN hα0 (mem_rad_of_pow_eq hτ) m hg σ

end Cyc

end RamanujanPetersson.EtCompact.Pur

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

/-- **`H` on `W₂`**: `m^* H · bW(φ₂ r)^N = (prdMap d)^* y` when `H · ρ(r)^N = ρ y`. -/
theorem wm_mG_H (r : k[X]) (N : ℕ)
    {y : Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)}
    {H : Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤)}
    (hH : H * (wm (R := R) (prdMap (toDG c hG₀) (opEt Uo))).appTop
      (gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R) r) ^ N =
      (wm (R := R) (prdMap (toDG c hG₀) (opEt Uo))).appTop y) :
    (wm (R := R) (mG c hle (chEt c φ₂) hD₂)).appTop H * (bW (Spec.map φ₂ ≫ c) (opEt Uo) R).hom (φ₂.hom r) ^ N =
      (wm (R := R) (prdMap d (opEt Uo))).appTop y := by
  rw [← wm_mG_gamMap c R hG₀ hle φ₂ hD₂ d r, ← map_pow, ← map_mul, hH, wm_mG_appTop c R hG₀ hle φ₂ hD₂ d]

end H

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Bd4 =====
section

/-!
# S4-EtPBC-A, O2 REL (O2Bd4): bad-point data with NO chart map to `D_{g₀}`; `exists_S4H'`

s128 fix of REL PLAN v2: a bad point `c(b)` has `g₀(b) = 0` (`c(D(g₀)) ⊆ U₀ ∪ {z}`), so no chart `D' ∋ b` maps to
`D_{g₀}`. The map `W(D') → Y₀` is `m^* ∘ ρ` instead (`m := mG : D' ×_P U₀ ⟶ D_G ×_P U₀`, `ρ := (prdMap (toDG c hG₀))^*`):
* **`wD_hom`**, **`shG_wm_any`**: `wm m ≫ shG φ₁ = shG φ₂` for ANY `m : D₂ ×_P U₀ ⟶ D₁ ×_P U₀` between chart products;
* **`mG_rho_gamMap`**, **`mG_H_any`**: `m^* (ρ r) = bW'(φ' r)`; the `H`-relation pulled back along `m`;
* **`exists_bad_e'`**: `exists_bad_e` (O2Bd2) without `d : D' ⟶ D_{g₀}`;
* **`exists_S4H'`**: `exists_S4H` (O2Gl2k) for a generic `G` (`hG₀ : g₀ ∣ G`), also returning `H ρ(t)^N = ρ(y)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.defProp false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

open scoped nonZeroDivisors

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap
  RamanujanPetersson.EtPBC.EtDeg

section WDHom

end WDHom

section AnyM

end AnyM

section BadChart'

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c] {Uo : P.Opens}
  (R : P.Etale) [IsAffine R.left] {g₀ G : k[X]} (hG₀ : g₀ ∣ G) (hle : opnDg c G ≤ Uo)
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).left]
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).left]
  {B' : CommRingCat.{0}} (φ' : CommRingCat.of k[X] ⟶ B') [Etale (Spec.map φ' ≫ c)]
  [IsAffine (prd (chEt c φ') (opEt Uo)).left]
  (hD' : ∀ v : (prd (chEt c φ') (opEt Uo)).left, (prd (chEt c φ') (opEt Uo)).hom v ∈ opnDg c G)

/-- `m^* (ρ r) = bW'(φ' r)` (`m := mG`, `ρ := (prdMap (toDG c hG₀))^*`). -/
theorem mG_rho_gamMap (r : k[X]) :
    (wm (R := R) (mG c hle (chEt c φ') hD')).appTop ((wm (R := R) (prdMap (toDG c hG₀) (opEt Uo))).appTop
      (gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R) r)) =
      (bW (Spec.map φ' ≫ c) (opEt Uo) R).hom (φ'.hom r) := by
  rw [appTop_gamMap _ _ (shG c (locF (B := CommRingCat.of k[X]) G) (Uo := Uo) R) (shG_wm c _ _ R (toDG c hG₀)) r,
    appTop_gamMap _ _ (shG c φ' (Uo := Uo) R) (shG_wm_any c R _ φ' (mG c hle (chEt c φ') hD')) r, gamMap_shG]

end BadChart'

section S4H'

end S4H'

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

include h₁₀ in
/-- **LocU** for `m = toOpEt ≫ σ`: maps into `opEt U₁` are unique. -/
theorem locCls_opn_toOpEt (hS₁ : (locC Λ D h₁).ShortExact) (hS : (locC Λ D h).ShortExact) {T : P.Etale}
    (σ : opEt U₁ ⟶ T) (hD : ∀ v : (prd D (opEt U₀)).left, (prd D (opEt U₀)).hom v ∈ U₁)
    {F : EtSh Λ P} (κ : Ext.{u} (freeSh Λ T) F 1) :
    hS.extClass.comp ((Ext.mk₀ (freeMap Λ (toOpEt (prd D (opEt U₀)) U₁ hD ≫ σ))).comp κ (zero_add 1))
        (show 1 + 1 = 2 from rfl) =
      hS₁.extClass.comp ((Ext.mk₀ (freeMap Λ (prT D (opEt U₁) ≫ σ))).comp κ (zero_add 1))
        (show 1 + 1 = 2 from rfl) :=
  locCls_opn_map h₁₀ h h₁ D hS₁ hS _ _ (by rw [← Category.assoc, opEt_ext (prdMapR D (opEtMap h₁₀) ≫ toOpEt (prd D (opEt U₀)) U₁ hD) (prT D (opEt U₁))]) κ

end LocU

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2PP5a =====
section

/-!
# S4-EtPBC-A, O2 PP' (O2PP5a): an `IsLoc` class at `c(a)` comes from a domain chart over a fixed cofinite `U₀`

* `prdTo`, `prdMapR_prdTo`: for `D` over `U₁ ∪ {z}` and `z ∉ U₀ ⊇ U₁`, `D ×_P U₀ ⟶ D ×_P U₁` splits `prdMapR`;
* `locCls_up`: `ε(D, U₁)∘κ = ε(D, U₀)∘Λ[prdTo]∘κ`;
* **`isLoc_chart`**: an `IsLoc` class at `z = c(a)` is `ε(chEt c φ, U₀)∘κ` for a chart `φ` with `B` a domain,
  given `g₀(a) ≠ 0` and `D_{g₀} ⊆ U₀ ∪ {z}` (`isLoc_aff_map`, shrink to `D_{φ g₀}`, `locCls_opn`, `locCls_up`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.EtDeg

universe u

section Up

variable {P : Scheme.{u}}

variable (D : P.Etale) {U₀ U₁ : P.Opens} (hD : ∀ v : (prd D (opEt U₀)).left, (prd D (opEt U₀)).hom v ∈ U₁)

/-- **Up**: `ε(D, U₁)∘κ = ε(D, U₀)∘Λ[prdTo]∘κ`. -/
theorem locCls_up {Λ : Type u} [CommRing Λ] {Uz : P.Opens} (h₁₀ : U₁ ≤ U₀) (h₀ : U₀ ≤ Uz) (h₁ : U₁ ≤ Uz)
    (hS₁ : (locC Λ D h₁).ShortExact) (hS : (locC Λ D h₀).ShortExact) {F : EtSh Λ P}
    (κ : Ext.{u} (freeSh Λ (prd D (opEt U₁))) F 1) :
    hS₁.extClass.comp κ (show 1 + 1 = 2 from rfl) =
      hS.extClass.comp ((Ext.mk₀ (freeMap Λ (prdTo D hD))).comp κ (zero_add 1)) (show 1 + 1 = 2 from rfl) := by
  rw [locCls_opn_map h₁₀ h₀ h₁ D hS₁ hS (prdTo D hD) (𝟙 _) (prdMapR_prdTo D hD h₁₀) κ, freeMap_id,
    Ext.mk₀_id_comp]

end Up

section Chart

end Chart

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L5c1 =====
section

/-!
# S4-EtPBC-A, L5c1 (Geo3): the Mayer-Vietoris square of the graph-open `D̃` on `P¹_S`

`K` algebraically closed, `z` a closed point of `P¹_K`, `σz : S ⟶ P¹_S` the horizontal section (L5a), `W` etale over
`P¹_S`, `Q ⊇ pr⁻¹ z` open:
* `σz` is a closed immersion (`isClosedImmersion_σz`); `Uz := pr⁻¹ (P¹ ∖ z)`;
* `D̃ := Dg W _ Q` (L5b) over `Zz := Zs σz qV W`, `D̃ₒ := D̃ ×_P Uz`, `Ũ := Zz ×_P Uz`;
* **`mvZ_shortExact`**: `0 → Λ[D̃ₒ] → Λ[D̃] ⊞ Λ[Ũ] → Λ[Zz] → 0` is short exact (MVG2 over `Uz`, MVG1 over `z` by the
  fibre lemma `graph_good` and `geom_factor`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3

universe u

section MVZ

variable (K : Type u) [Field K] [IsAlgClosed K] {S : Scheme.{u}} (gS : S ⟶ Spec (CommRingCat.of K))
  (z : P1 K) (hz : IsClosed ({z} : Set (P1 K)))

instance isClosedImmersion_σz : IsClosedImmersion (σz K gS z hz) := by
  have : IsClosedImmersion (σz K gS z hz ≫ qV K gS) := by rw [σz_qV]; infer_instance
  exact IsClosedImmersion.of_comp (σz K gS z hz) (qV K gS)

/-- `pr⁻¹ (P¹ ∖ z)`. -/
def Uz : (PV K gS).Opens := ⟨pr K gS ⁻¹' {z}ᶜ, hz.isOpen_compl.preimage (pr K gS).continuous⟩

omit [IsAlgClosed K] in
theorem mem_Uz (x : PV K gS) : x ∈ Uz K gS z hz ↔ pr K gS x ≠ z := Iff.rfl

/-- A point off `Uz` gives a geometric point factoring through `σz`. -/
theorem pt_factor_σz (x : PV K gS) (hx : x ∉ Uz K gS z hz) :
    (geomPtAt x).pt = ((geomPtAt x).pt ≫ qV K gS) ≫ σz K gS z hz := by
  refine geom_factor K gS z hz _ ?_
  have h1 : (geomPtAt x).pt (IsLocalRing.closedPoint (geomPtAt x).Ω) = x :=
    (congrArg (geomPtAt x).pt (spec_pt_eq _ _)).trans (center_geomPtAt x)
  rw [h1]
  exact not_not.1 hx

variable (W : (PV K gS).Etale) (Q : (PV K gS).Opens)

/-- `D̃`. -/
abbrev Dz : (PV K gS).Etale := Dg W (σz_qV K gS z hz) Q

/-- `Zz = (W ×_P S) ×_S P`. -/
abbrev Zz : (PV K gS).Etale := Zs (σz K gS z hz) (qV K gS) W

/-- `D̃ ⟶ Zz`. -/
abbrev wz : Dz K gS z hz W Q ⟶ Zz K gS z hz W := wg W (σz_qV K gS z hz) Q

/-- `D̃ₒ ⟶ Ũ`. -/
abbrev p₂z : prd (Dz K gS z hz W Q) (opEt (Uz K gS z hz)) ⟶ prd (Zz K gS z hz W) (opEt (Uz K gS z hz)) :=
  prdMap (wz K gS z hz W Q) (opEt (Uz K gS z hz))

theorem sqz : prW (Dz K gS z hz W Q) (opEt (Uz K gS z hz)) ≫ wz K gS z hz W Q =
    p₂z K gS z hz W Q ≫ prW (Zz K gS z hz W) (opEt (Uz K gS z hz)) :=
  (prdMap_prW (wz K gS z hz W Q) (opEt (Uz K gS z hz))).symm

theorem mvZ_good (hQ : ∀ x : PV K gS, pr K gS x = z → x ∈ Q) (x : PV K gS)
    (c : (geomPtAt x).point.fiber.obj (Zz K gS z hz W)) :
    MVG1 ((geomPtAt x).point.fiber.map (p₂z K gS z hz W Q)) ((geomPtAt x).point.fiber.map (wz K gS z hz W Q))
        ((geomPtAt x).point.fiber.map (prW (Zz K gS z hz W) (opEt (Uz K gS z hz)))) c ∨
      MVG2 ((geomPtAt x).point.fiber.map (prW (Dz K gS z hz W Q) (opEt (Uz K gS z hz))))
        ((geomPtAt x).point.fiber.map (wz K gS z hz W Q))
        ((geomPtAt x).point.fiber.map (prW (Zz K gS z hz W) (opEt (Uz K gS z hz)))) c := by
  by_cases hx : x ∈ Uz K gS z hz
  · right
    obtain ⟨t⟩ := nonempty_fib_opEt (Uz K gS z hz) x hx
    have hv := prW_bijective (Zz K gS z hz W) (opEt (Uz K gS z hz)) x t
    have hp := prW_bijective (Dz K gS z hz W Q) (opEt (Uz K gS z hz)) x t
    exact ⟨fun b b' hb hb' => hv.1 (hb.trans hb'.symm), hv.2 c, fun a _ => hp.existsUnique a⟩
  · left
    have hxσ := pt_factor_σz K gS z hz x hx
    have hxQ : x ∈ Q := hQ x (not_not.1 hx)
    obtain ⟨h1, h2⟩ := graph_good W (σz_qV K gS z hz) Q x hxσ hxQ c
    have := isEmpty_fib_prd (Zz K gS z hz W) (Uz K gS z hz) x hx
    exact ⟨h1, h2, fun b _ => isEmptyElim b⟩

end MVZ

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L5c2 =====
section

/-!
# S4-EtPBC-A, L5c2: the family point class `αZ` on `P¹_S` at a chart point

`c : A¹_K ⟶ P¹_K` an open chart, `z = c (a)`, `Qc = pr⁻¹ (range c)`; `D̃ₒ = D̃ ×_P Uz` (L5c1) maps into the punctured
chart `Spec K[X]_{X-a}` (`fA`, `fA_fac`), giving the Kummer class `κZ c' = fA^* ξ_a(c')` and
* **`αZ c' := ε(D̃, Ũ) ∘ θ(D̃ₒ ⟶ D̃, κZ c') ∘ Λ[D̃ ⟶ W] ∈ Ext²(Λ[Zz], Λ[W])`**.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Polynomial Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3

section Chart

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (c : A1 K ⟶ P1 K) [IsOpenImmersion c] (a : K) (W : (PV K gS).Etale)

/-- `pr⁻¹ (range c)`. -/
def Qc : (PV K gS).Opens := pr K gS ⁻¹ᵁ c.opensRange

omit [IsAlgClosed K] in
theorem hQc (x : PV K gS) (hx : pr K gS x = c (A1pt K a)) : x ∈ Qc gS c := ⟨A1pt K a, hx.symm⟩

/-- `D̃ₒ = D̃ ×_P Uz` at the chart point `c a`. -/
abbrev DzO : (PV K gS).Etale :=
  prd (Dz K gS (c (A1pt K a)) (chart_hclA c a) W (Qc gS c)) (opEt (Uz K gS (c (A1pt K a)) (chart_hclA c a)))

theorem DzO_mem (y : (DzO gS c a W).left) :
    (DzO gS c a W).hom y ∈ Uz K gS (c (A1pt K a)) (chart_hclA c a) ∧ (DzO gS c a W).hom y ∈ Qc gS c := by
  obtain ⟨b, -⟩ := exists_fib_over (DzO gS c a W) y
  set x := (DzO gS c a W).hom y
  refine ⟨mem_of_fib_opEt _ x ((geomPtAt x).point.fiber.map (prT _ _) b), ?_⟩
  set d := (geomPtAt x).point.fiber.map (prW _ _) b
  have h1 := opnι_mem _ _ (fpt x d)
  rw [← fib_left_map] at h1
  exact (congrArg (· ∈ (Qc gS c : Set (PV K gS))) (fib_over x _)).mp h1.2

theorem range_DzO :
    Set.range ((DzO gS c a W).hom ≫ pr K gS) ⊆
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap K[X] (LA K a))) ≫ c) := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨hU, hQ⟩ := DzO_mem gS c a W y
  obtain ⟨p, hp⟩ : pr K gS ((DzO gS c a W).hom y) ∈ Set.range c := hQ
  have hpa : (X - C a : K[X]) ∉ p.asIdeal := by
    intro hmem
    have hm : (Ideal.span {X - C a} : Ideal K[X]).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C a)
    have he : p = A1pt K a := PrimeSpectrum.ext
      (hm.eq_of_le p.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hmem)).symm
    exact hU (hp.symm.trans (congrArg c he))
  have hr : p ∈ Set.range (PrimeSpectrum.comap (algebraMap K[X] (LA K a))) := by
    rw [PrimeSpectrum.localization_away_comap_range (LA K a) (X - C a : K[X])]
    exact hpa
  obtain ⟨q, hq⟩ := hr
  exact ⟨q, (Scheme.Hom.comp_apply _ _ _).trans ((congrArg c hq).trans (hp.trans (Scheme.Hom.comp_apply _ _ _).symm))⟩

/-- `D̃ₒ ⟶ Spec K[X]_{X-a}`. -/
def fA : (DzO gS c a W).left ⟶ Spec (CommRingCat.of (LA K a)) :=
  IsOpenImmersion.lift (Spec.map (CommRingCat.ofHom (algebraMap K[X] (LA K a))) ≫ c) _ (range_DzO gS c a W)

theorem fA_fac : fA gS c a W ≫ Spec.map (CommRingCat.ofHom (algebraMap K[X] (LA K a))) ≫ c =
    (DzO gS c a W).hom ≫ pr K gS :=
  IsOpenImmersion.lift_fac _ _ _

variable {N : ℕ} [NeZero N] (hN : (N : K) ≠ 0) (Λ : Type) [CommRing Λ] (hΛ : ∀ x : Λ, N • x = 0)

/-- The Kummer class `κZ c' = fA^* ξ_a(c')` on `D̃ₒ`. -/
def κZ (c' : Λ) : H Λ (unitSh Λ (DzO gS c a W).left) 1 := pullH Λ (fA gS c a W) 1 (xiA a hN Λ hΛ c')

end Chart

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L6b1 =====
section

/-!
# S4-EtPBC-A, L6b1: the `K`-rational fibre `ι' : P¹_K ⟶ P¹_S` and the horizontal section `σ'` of `ι'^* Zz`

* `toPull f m hm : T' ⟶ (etPull f).obj Y'` from `m : T'.left ⟶ Y'.left` over `f` (`toPull_fst`, `toPull_comp`,
  `toPull_map`);
* `sK = inv (s.pt ≫ gS) ≫ s.pt : Spec K ⟶ S`, `ιP : P¹_K ⟶ P¹_S` (`ιP_pr`, `ιP_qV`, `ptz_ιP : ptz ≫ ιP = sK ≫ σz`);
* for a `K`-point `v'` of `Vs = W ×_P S` over `sK`: `σ₀ v' : P¹_K ⟶ Zz` and `σP v' : etId P¹_K ⟶ ιP^* Zz`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3

universe u

section ToPull

end ToPull

section Fib

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)]

/-- The `K`-point of `S` under `s`. -/
def sK : Spec (CommRingCat.of K) ⟶ S := inv (s.pt ≫ gS) ≫ s.pt

theorem sK_gS : sK gS s ≫ gS = 𝟙 _ := by
  rw [sK, Category.assoc, IsIso.inv_hom_id]

/-- The `K`-rational fibre `P¹_K ⟶ P¹_S` over `sK`. -/
def ιP : P1 K ⟶ PV K gS :=
  pullback.lift (𝟙 _) (P1.toSpecK K ≫ sK gS s)
    (by rw [Category.id_comp, Category.assoc, sK_gS, Category.comp_id])

@[reassoc]
theorem ιP_pr : ιP gS s ≫ pr K gS = 𝟙 _ := pullback.lift_fst _ _ _

@[reassoc]
theorem ιP_qV : ιP gS s ≫ qV K gS = P1.toSpecK K ≫ sK gS s := pullback.lift_snd _ _ _

theorem ptz_ιP (z : P1 K) (hz : IsClosed ({z} : Set (P1 K))) :
    ptz K z hz ≫ ιP gS s = sK gS s ≫ σz K gS z hz := by
  apply pullback.hom_ext
  · rw [Category.assoc, ιP_pr, Category.comp_id, Category.assoc, σz_pr, ← Category.assoc, sK_gS,
      Category.id_comp]
  · rw [Category.assoc, ιP_qV, ← Category.assoc, ptz_toSpecK, Category.id_comp, Category.assoc, σz_qV,
      Category.comp_id]

variable (c : A1 K ⟶ P1 K) [IsOpenImmersion c] (a : K) (W : (PV K gS).Etale)

/-- The horizontal section `P¹_K ⟶ Zz` through a `K`-point `v'` of `Vs` over `sK`. -/
def σ₀ (v' : Spec (CommRingCat.of K) ⟶ (Vs (σz K gS (zc c a) (chart_hclA c a)) W).left)
    (hv' : v' ≫ (Vs (σz K gS (zc c a) (chart_hclA c a)) W).hom = sK gS s) :
    P1 K ⟶ pullback (Vs (σz K gS (zc c a) (chart_hclA c a)) W).hom (qV K gS) :=
  pullback.lift (P1.toSpecK K ≫ v') (ιP gS s)
    ((Category.assoc _ _ _).trans ((whisker_eq _ hv').trans (ιP_qV gS s).symm))

theorem σ₀_fst (v' : Spec (CommRingCat.of K) ⟶ (Vs (σz K gS (zc c a) (chart_hclA c a)) W).left)
    (hv' : v' ≫ (Vs (σz K gS (zc c a) (chart_hclA c a)) W).hom = sK gS s) :
    σ₀ gS s c a W v' hv' ≫ pullback.fst _ (qV K gS) = P1.toSpecK K ≫ v' := pullback.lift_fst _ _ _

theorem σ₀_snd (v' : Spec (CommRingCat.of K) ⟶ (Vs (σz K gS (zc c a) (chart_hclA c a)) W).left)
    (hv' : v' ≫ (Vs (σz K gS (zc c a) (chart_hclA c a)) W).hom = sK gS s) :
    σ₀ gS s c a W v' hv' ≫ pullback.snd _ (qV K gS) = ιP gS s := pullback.lift_snd _ _ _

/-- **The section `σ' : etId P¹_K ⟶ ιP^* Zz`.** -/
def σP (v' : Spec (CommRingCat.of K) ⟶ (Vs (σz K gS (zc c a) (chart_hclA c a)) W).left)
    (hv' : v' ≫ (Vs (σz K gS (zc c a) (chart_hclA c a)) W).hom = sK gS s) :
    etId (P1 K) ⟶ (etPull (ιP gS s)).obj (Zz K gS (zc c a) (chart_hclA c a) W) :=
  toPull (ιP gS s) (σ₀ gS s c a W v' hv') ((σ₀_snd gS s c a W v' hv').trans (Category.id_comp _).symm)

end Fib

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L6b2 =====
section

/-!
# S4-EtPBC-A, L6b2: the `D` side of the comparison on `P¹_K`

For a chart `D = chEt c φ` (`B` Dedekind, `(X - a)` a nonzero prime) and `s' : D ⟶ ιP^* W`:
* the point `d₀ = (X - a)` of `D` over `z = c a` and its `K`-point `δ₀` (`δ₀_hom : δ₀ ≫ D.hom = ptz`);
* `wK = s'(d₀)`, the `K`-point `v'` of `Vs` over `sK` (`v'_hom`), `gE₀ : D ⟶ Es` (`v ↦ (s' v, σ₀ v)`);
* `Vb = gE₀⁻¹(Og)`, `Db = opn D Vb` (`d₀ ∈ Vb`), its fibre at `z` (subsingleton, nonempty) and `hSb`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum

section Sq

end Sq

section Pt

end Pt

section Fib

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)] (c : A1 K ⟶ P1 K) [IsOpenImmersion c] (a : K) (W : (PV K gS).Etale)
  {B : CommRingCat.{0}} (φ : CommRingCat.of K[X] ⟶ B) [Etale (Spec.map φ ≫ c)] [IsDedekindDomain B]
  (ht : φ.hom (X - C a) ≠ 0) (hP : (Ideal.span {φ.hom (X - C a)}).IsPrime)
  (s' : chEt c φ ⟶ (etPull (ιP gS s)).obj W)

/-- `wK = s'(d₀) : Spec K ⟶ W`. -/
def wK : Spec (CommRingCat.of K) ⟶ W.left :=
  δ₀ c a φ ht hP ≫ s'.left ≫ pullback.fst W.hom (ιP gS s)

theorem wK_hom : wK gS s c a W φ ht hP s' ≫ W.hom = sK gS s ≫ σz K gS (zc c a) (chart_hclA c a) :=
  (Category.assoc _ _ _).trans ((whisker_eq _ (pullPt_sq (ιP gS s) W s')).trans
    ((Category.assoc _ _ _).symm.trans ((eq_whisker (δ₀_hom c a φ ht hP) _).trans
      (ptz_ιP gS s (zc c a) (chart_hclA c a)))))

/-- The `K`-point `v'` of `Vs` over `sK`. -/
def v' : Spec (CommRingCat.of K) ⟶ (Vs (σz K gS (zc c a) (chart_hclA c a)) W).left :=
  pullback.lift (wK gS s c a W φ ht hP s') (sK gS s) (wK_hom gS s c a W φ ht hP s')

theorem v'_hom : v' gS s c a W φ ht hP s' ≫ (Vs (σz K gS (zc c a) (chart_hclA c a)) W).hom = sK gS s :=
  pullback.lift_snd _ _ _

theorem v'_fst : v' gS s c a W φ ht hP s' ≫ pullback.fst W.hom (σz K gS (zc c a) (chart_hclA c a)) =
    wK gS s c a W φ ht hP s' :=
  pullback.lift_fst _ _ _

/-- `σ₀` at `v'`. -/
abbrev σ₁ : P1 K ⟶ pullback (Vs (σz K gS (zc c a) (chart_hclA c a)) W).hom (qV K gS) :=
  σ₀ gS s c a W (v' gS s c a W φ ht hP s') (v'_hom gS s c a W φ ht hP s')

end Fib

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L6b3 =====
section

/-!
# S4-EtPBC-A, L6b3: the morphism of MV data `locC(D♭) ⟶ ιP^* MVZ` on `P¹_K`

`a' : D♭ ×_P Uz' ⟶ ιP^* DzO`, `a : D♭ ⟶ ιP^* Dz`, `b : Uz' ⟶ ιP^*(Zz ×_P Uz)`, `c := σP`, with the four squares
`h₁ .. h₄` (all proved on underlying scheme maps through `toPull`), and **`mvTheta_Db`**:
`Λ[σP] ∘ (ιP^*MVZ-class of κ, r) = (locC D♭-class of a'^*κ, a ≫ r)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Polynomial Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtCompact.GalTrE

section Mor

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)] (c : A1 K ⟶ P1 K) [IsOpenImmersion c] (a : K) (W : (PV K gS).Etale)
  {B : CommRingCat.{0}} (φ : CommRingCat.of K[X] ⟶ B) [Etale (Spec.map φ ≫ c)] [IsDedekindDomain B]
  (ht : φ.hom (X - C a) ≠ 0) (hP : (Ideal.span {φ.hom (X - C a)}).IsPrime)
  (s' : chEt c φ ⟶ (etPull (ιP gS s)).obj W)
  (Uz' : (P1 K).Opens) (hUz' : ∀ x : P1 K, x ∈ Uz' ↔ x ≠ zc c a)

include hUz' in
theorem Uz'_le : Uz' ≤ ιP gS s ⁻¹ᵁ Uz K gS (zc c a) (chart_hclA c a) := fun x hx => by
  have h : pr K gS (ιP gS s x) = x := by
    rw [← Scheme.Hom.comp_apply, ιP_pr]; rfl
  show pr K gS (ιP gS s x) ≠ zc c a
  rw [h]; exact (hUz' x).mp hx

/-- `ιP : Uz' ⟶ Uz`. -/
def ιU : Uz'.toScheme ⟶ (Uz K gS (zc c a) (chart_hclA c a)).toScheme :=
  (ιP gS s).resLE (Uz K gS (zc c a) (chart_hclA c a)) Uz' (Uz'_le gS s c a Uz' hUz')

theorem ιU_eq : ιU gS s c a Uz' hUz' ≫ (Uz K gS (zc c a) (chart_hclA c a)).ι ≫ 𝟙 (PV K gS) =
    (Uz'.ι ≫ 𝟙 (P1 K)) ≫ ιP gS s := by
  simp only [Category.comp_id, ιU, Scheme.Hom.resLE_comp_ι]

end Mor

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L6c1 =====
section

/-!
# S4-EtPBC-A, L6c1: a point class on `P¹_K` through the family square

For the data of a point class `x = pcD c' ∘ Λ[s']` with coefficients `T = ιP^* W`:
* `pcD_s'`: `x = ε(locC D) ∘ θ(prW, κ_D) ∘ Λ[s']`, `κ_D = isoT⁻¹^* toWa^* ξ`;
* `shrink_Db`: the same class through `D♭ = opn D Vb`;
* `hrM : aM ≫ ιP^*(rW) = opnι ≫ s'`, `hmapA`, `hκ` (the Kummer classes agree on `D♭ ×_P Uz'`);
* **`ptCls_Db`**: `x = Λ[σP] ∘ (ιP^*MVZ-class of fW^* κZ and ιP^* rW)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Polynomial Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtCompact.GalTrE

section Cls

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)] (c : A1 K ⟶ P1 K) [IsOpenImmersion c] (a : K) (W : (PV K gS).Etale)
  {B : CommRingCat.{0}} (φ : CommRingCat.of K[X] ⟶ B) [Etale (Spec.map φ ≫ c)] [IsDedekindDomain B]
  (ht : φ.hom (X - C a) ≠ 0) (hP : (Ideal.span {φ.hom (X - C a)}).IsPrime)
  (s' : chEt c φ ⟶ (etPull (ιP gS s)).obj W)
  (Uz' : (P1 K).Opens) (hUz' : ∀ x : P1 K, x ∈ Uz' ↔ x ≠ zc c a)
  {N : ℕ} [NeZero N] (hN : (N : K) ≠ 0) (Λ : Type) [CommRing Λ] (hΛ : ∀ x : Λ, N • x = 0)
  (hUz : ∀ u : Spec B, (chEt c φ).hom u ∈ Uz' ↔ φ.hom (X - C a) ∉ u.asIdeal)
  (hS : (locC Λ (chEt c φ) (le_refl Uz')).ShortExact) (c' : Λ)

/-- `rW : Dz ⟶ W`. -/
abbrev rW : Dz K gS (zc c a) (chart_hclA c a) W (Qc gS c) ⟶ W :=
  opnι _ _ ≫ prW W (Zz K gS (zc c a) (chart_hclA c a) W)

end Cls

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L7b1 =====
section

/-!
# S4-EtPBC-A, O2 L7b1: the transport `Tr` from `P¹_K` to the fibre `P_s`
For a `K`-rational geometric point `s` (`[IsIso (s.pt ≫ gS)]`), `e := fibToP1 : P_s ⟶ P¹_K` is an isomorphism with
`e ≫ ιP = ι` (`fibToP1_ιP`). Base change identifications `isoE X : e^*ιP^*X ⟶ ι^*X` (natural, invertible),
the section `σG` of `ιP^*(qV^*V)` through a `K`-point `v'` of `V`, the neighbourhood `jG = (V, v')` of `s`, and
**`nbhdSec_eq`**: `nbhdSec jG = c₀ ≫ e^*σG ≫ isoE`. **`TrE`**: `Ext²(Λ[P¹], Λ[ιP^*R]) → Ext²(Λ_{P_s}, ι^*Λ[R])`,
`x ↦ u ∘ e^*x ∘ v`; **`TrE_surjective`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtCompact.GalTrE

universe u

section Gen

end Gen

section GenSurj

universe w v₁ u₁ v₂ u₂

end GenSurj

section Fib

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)]

theorem fibToP1_toSpecK : fibToP1 K gS s ≫ P1.toSpecK K = (pullback.snd (qV K gS) s.pt ≫ s.pt) ≫ gS :=
  ((Category.assoc _ _ _).trans (whisker_eq _ pullback.condition)).trans
    ((Category.assoc _ _ _).symm.trans (eq_whisker pullback.condition gS))

/-- **`e ≫ ιP = ι`** for `e := fibToP1`. -/
theorem fibToP1_ιP : fibToP1 K gS s ≫ ιP gS s = fibι (qV K gS) s := by
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans ((whisker_eq _ (ιP_pr gS s)).trans (Category.comp_id _))
  · have hk : s.pt ≫ gS ≫ inv (s.pt ≫ gS) ≫ s.pt = s.pt :=
      (Category.assoc _ _ _).symm.trans (IsIso.hom_inv_id_assoc _ _)
    calc (fibToP1 K gS s ≫ ιP gS s) ≫ pullback.snd (P1.toSpecK K) gS
        = (fibToP1 K gS s ≫ P1.toSpecK K) ≫ sK gS s := by
          rw [Category.assoc, Category.assoc]
          exact whisker_eq _ (ιP_qV gS s)
      _ = pullback.snd (qV K gS) s.pt ≫ s.pt := by
          rw [fibToP1_toSpecK, sK]
          simp only [Category.assoc, hk]
      _ = _ := pullback.condition.symm

/-- `e^*ιP^*X ⟶ ι^*X`. -/
def isoE (X : (PV K gS).Etale) :
    (etPull (fibToP1 K gS s)).obj ((etPull (ιP gS s)).obj X) ⟶ (etPull (fibι (qV K gS) s)).obj X :=
  (etPullCompIso (fibToP1 K gS s) (ιP gS s)).inv.app X ≫ etPullCongr (fibToP1_ιP gS s) X

instance isoE_isIso (X : (PV K gS).Etale) : IsIso (isoE gS s X) := by
  unfold isoE
  infer_instance

theorem isoE_natural {X X' : (PV K gS).Etale} (m : X ⟶ X') :
    (etPull (fibToP1 K gS s)).map ((etPull (ιP gS s)).map m) ≫ isoE gS s X' =
      isoE gS s X ≫ (etPull (fibι (qV K gS) s)).map m :=
  (Category.assoc _ _ _).symm.trans ((eq_whisker ((etPullCompIso (fibToP1 K gS s) (ιP gS s)).inv.naturality m) _).trans
    ((Category.assoc _ _ _).trans ((whisker_eq _ (etPullCongr_natural (fibToP1_ιP gS s) m)).trans
      (Category.assoc _ _ _).symm)))

theorem isoE_left_fst (X : (PV K gS).Etale) :
    (isoE gS s X).left ≫ pullback.fst X.hom (fibι (qV K gS) s) =
      pullback.fst ((etPull (ιP gS s)).obj X).hom (fibToP1 K gS s) ≫ pullback.fst X.hom (ιP gS s) :=
  (Category.assoc _ _ _).trans ((whisker_eq _ (etPullCongr_left_fst (fibToP1_ιP gS s) X)).trans
    (etPullCompIso_inv_fst (fibToP1 K gS s) (ιP gS s) X))

theorem isoE_left_fW (X : (PV K gS).Etale) :
    (isoE gS s X).left ≫ fW (fibι (qV K gS) s) X = fW (fibToP1 K gS s) ((etPull (ιP gS s)).obj X) ≫ fW (ιP gS s) X :=
  isoE_left_fst gS s X

/-- `P¹_K ⟶ qV^*V` through a `K`-point `v'` of `V` over `sK`. -/
def σ₀G (V : S.Etale) (v' : Spec (CommRingCat.of K) ⟶ V.left) (hv' : v' ≫ V.hom = sK gS s) :
    P1 K ⟶ pullback V.hom (qV K gS) :=
  pullback.lift (P1.toSpecK K ≫ v') (ιP gS s) ((Category.assoc _ _ _).trans ((whisker_eq _ hv').trans (ιP_qV gS s).symm))

/-- The section `etId P¹_K ⟶ ιP^*(qV^*V)`. -/
def σG (V : S.Etale) (v' : Spec (CommRingCat.of K) ⟶ V.left) (hv' : v' ≫ V.hom = sK gS s) :
    etId (P1 K) ⟶ (etPull (ιP gS s)).obj ((etPull (qV K gS)).obj V) :=
  toPull (ιP gS s) (σ₀G gS s V v' hv') ((pullback.lift_snd _ _ _).trans (Category.id_comp _).symm)

theorem σP_eq (c : A1 K ⟶ P1 K) [IsOpenImmersion c] (a : K) (W : (PV K gS).Etale)
    (v' : Spec (CommRingCat.of K) ⟶ (Vs (σz K gS (zc c a) (chart_hclA c a)) W).left)
    (hv' : v' ≫ (Vs (σz K gS (zc c a) (chart_hclA c a)) W).hom = sK gS s) :
    σP gS s c a W v' hv' = σG gS s (Vs (σz K gS (zc c a) (chart_hclA c a)) W) v' hv' := rfl

theorem jG_w (V : S.Etale) (v' : Spec (CommRingCat.of K) ⟶ V.left) (hv' : v' ≫ V.hom = sK gS s) :
    ((s.pt ≫ gS) ≫ v') ≫ V.hom = s.pt :=
  (Category.assoc _ _ _).trans ((whisker_eq _ hv').trans (IsIso.hom_inv_id_assoc _ _))

/-- The etale neighbourhood `(V, v')` of `s`. -/
def jG (V : S.Etale) (v' : Spec (CommRingCat.of K) ⟶ V.left) (hv' : v' ≫ V.hom = sK gS s) : Nbhd s :=
  s.point.fiber.elementsMk V (CategoryTheory.Over.homMk ((s.pt ≫ gS) ≫ v') (jG_w gS s V v' hv') :
    CategoryTheory.Over.mk s.pt ⟶ (Scheme.Etale.forget S).obj V)

theorem fibToNbhd_jG (V : S.Etale) (v' : Spec (CommRingCat.of K) ⟶ V.left) (hv' : v' ≫ V.hom = sK gS s) :
    fibToNbhd (qV K gS) s (jG gS s V v' hv') = fibToP1 K gS s ≫ σ₀G gS s V v' hv' := by
  apply pullback.hom_ext
  · refine (fibToNbhd_fst (qV K gS) s _).trans ?_
    show pullback.snd (qV K gS) s.pt ≫ ((s.pt ≫ gS) ≫ v') =
      (fibToP1 K gS s ≫ σ₀G gS s V v' hv') ≫ pullback.fst V.hom (qV K gS)
    have h2 : σ₀G gS s V v' hv' ≫ pullback.fst V.hom (qV K gS) = P1.toSpecK K ≫ v' := pullback.lift_fst _ _ _
    have h3 : (fibToP1 K gS s ≫ σ₀G gS s V v' hv') ≫ pullback.fst V.hom (qV K gS) =
        ((pullback.snd (qV K gS) s.pt ≫ s.pt) ≫ gS) ≫ v' :=
      (Category.assoc _ _ _).trans ((whisker_eq _ h2).trans ((Category.assoc _ _ _).symm.trans
        (eq_whisker (fibToP1_toSpecK gS s) v')))
    exact (h3.trans ((eq_whisker (Category.assoc _ _ _) v').trans (Category.assoc _ _ _))).symm
  · refine (fibToNbhd_snd (qV K gS) s _).trans ?_
    show fibι (qV K gS) s = (fibToP1 K gS s ≫ σ₀G gS s V v' hv') ≫ pullback.snd V.hom (qV K gS)
    exact (fibToP1_ιP gS s).symm.trans ((whisker_eq _ (pullback.lift_snd _ _ _)).symm.trans (Category.assoc _ _ _).symm)

variable (Λ : Type) [CommRing Λ]

/-- `Λ_{P_s} ⟶ e^*Λ[P¹_K]`. -/
def uE : unitSh Λ (fib (qV K gS) s) ⟶ (pull (fibToP1 K gS s) Λ).obj (freeSh Λ (etId (P1 K))) :=
  (unitIso Λ (fib (qV K gS) s)).inv ≫ freeMap Λ (etIdPull (fibToP1 K gS s)).hom ≫
    pullFreeHom Λ (fibToP1 K gS s) (etId (P1 K))

/-- `e^*Λ[ιP^*R] ⟶ ι^*Λ[R]`. -/
def vE (R : (PV K gS).Etale) :
    (pull (fibToP1 K gS s) Λ).obj (freeSh Λ ((etPull (ιP gS s)).obj R)) ⟶ (pull (fibι (qV K gS) s) Λ).obj (freeSh Λ R) :=
  inv (pullFreeHom Λ (fibToP1 K gS s) ((etPull (ιP gS s)).obj R)) ≫ freeMap Λ (isoE gS s R) ≫
    pullFreeHom Λ (fibι (qV K gS) s) R

instance uE_isIso : IsIso (uE gS s Λ) := by
  unfold uE
  infer_instance

instance vE_isIso (R : (PV K gS).Etale) : IsIso (vE gS s Λ R) := by
  unfold vE
  infer_instance

end Fib

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L7b2 =====
section

/-!
# S4-EtPBC-A, O2 L7b2: transport of family MV-theta classes
**`TrE_mvTheta`**: for an MV square over `qV^*V` on `P = P¹_K ×_K S` and a `K`-point `v'` of `V` over `s`, the
transport `TrE` of the `P¹_K`-class `Λ[σG] ∘ ιP^*(ε ∘ θ(p₁, κ) ∘ Λ[r])` is the base change at `jG = (V, v')` of the
family class `ε ∘ θ(p₁, κ) ∘ Λ[r]`. Proof: `mvThetaR_pull` along `e`, `bc_mvThetaR` at `jG`, and `mvTheta_map` along
the base change identifications `isoE` (`nbhdSec_eq`, `isoE_natural`, `isoE_left_fW`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtCompact.GalTrE

universe w v₀ u₀

section GenTr

universe w' v₁ u₁ v₂ u₂

end GenTr

section TrMV

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)] (Λ : Type) [CommRing Λ]
  (V : S.Etale) (v' : Spec (CommRingCat.of K) ⟶ V.left) (hv' : v' ≫ V.hom = sK gS s)

theorem uE_comp {T : (P1 K).Etale} (σ : etId (P1 K) ⟶ T) :
    uE gS s Λ ≫ (pull (fibToP1 K gS s) Λ).map (freeMap Λ σ) =
      ((unitIso Λ (fib (qV K gS) s)).inv ≫ freeMap Λ ((etIdPull (fibToP1 K gS s)).hom ≫
        (etPull (fibToP1 K gS s)).map σ)) ≫ pullFreeHom Λ (fibToP1 K gS s) T := by
  have h := pullFreeHom_natural (Λ := Λ) (fibToP1 K gS s) σ
  rw [uE, freeMap_comp]
  simp only [Category.assoc]
  rw [← h]

theorem vE_tail (R : (PV K gS).Etale) {X : (fib (pullback.snd (P1.toSpecK K) gS) s).Etale}
    (a : X ⟶ (etPull (fibToP1 K gS s)).obj ((etPull (ιP gS s)).obj R)) :
    (freeMap Λ a ≫ pullFreeHom Λ (fibToP1 K gS s) ((etPull (ιP gS s)).obj R)) ≫ vE gS s Λ R =
      freeMap Λ (a ≫ isoE gS s R) ≫ pullFreeHom Λ (fibι (qV K gS) s) R := by
  rw [vE, freeMap_comp]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]

end TrMV

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L7c1 =====
section

/-!
# S4-EtPBC-A, O2 L7c1: the transport `TrE` as an additive map; point classes transport into germs
* `TrEh`: `TrE` as an additive map (built from `Ext.bilinearComp` and `mapExtAddHom`, so `TrEh x = TrE x` is `rfl`);
* `isClosedImmersion_ιP`: `ιP : P¹_K ⟶ P¹_S` is a closed immersion (`ι = e ≫ ιP`, `e` an isomorphism);
* `isAffine_ιPW`: `ιP^*W` is affine for `W` affine;
* **`ptCls_bcImg`**: `TrE` of a point class of `Λ[ιP^*W]` is the base change of the family class `αZ` at `jG`
  (`ptCls_Db`, `σP_eq`, `TrE_mvTheta`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtCompact.GalTrE

section L7c1

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)] (Λ : Type) [CommRing Λ]

theorem isClosedImmersion_ιP : IsClosedImmersion (ιP gS s) := by
  have : IsClosedImmersion s.pt := T3d.isClosedImmersion_of_isIso_comp gS s.pt
  have : IsClosedImmersion (fibι (qV K gS) s) := T3d.isClosedImmersion_fibι (qV K gS) s
  have h : ιP gS s = inv (fibToP1 K gS s) ≫ fibι (qV K gS) s := by
    rw [← fibToP1_ιP gS s, IsIso.inv_hom_id_assoc]
  rw [h]
  infer_instance

theorem isAffine_ιPW (W : (PV K gS).Etale) [IsAffine W.left] : IsAffine ((etPull (ιP gS s)).obj W).left := by
  have := isClosedImmersion_ιP gS s
  rw [etPull_obj_left]
  have : IsAffine ((𝟭 Scheme).obj W.left) := ‹IsAffine W.left›
  have : IsClosedImmersion (pullback.fst W.hom (ιP gS s)) := inferInstance
  exact (IsClosedImmersion.isAffine_surjective_of_isAffine (pullback.fst W.hom (ιP gS s))).1

end L7c1

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L8a =====
section

/-!
# S4-EtPBC-A, O2 L8a: finite coproducts, and the transport `TrG` for every sheaf on `P¹_S`
* **`Delta.surjAt_coprod`**: surjectivity on germs passes to finite coproducts (`ι : Type`, finite);
* `wGIso`, `wG`, `wG_natural`: `e^* ιP^* G ≅ ι^* G` (`e = fibToP1`, `e ≫ ιP = ι`), natural in `G`;
* **`TrG`** `G x = u ∘ e^*x ∘ wG`: `Ext²(Λ[P¹_K], ιP^*G) → Ext²(Λ_{P_s}, ι^*G)`; `TrGh` (additive, `rfl`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.Delta

universe w v₁ u₁ v₂ u₂ v₃ u₃

end RamanujanPetersson.EtPBC.Delta

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtCompact.GalTrE
  RamanujanPetersson.EtCompact.PushBC

universe u

section TrG

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)] (Λ : Type) [CommRing Λ]

/-- `e^* ιP^* G ≅ ι^* G`. -/
def wGIso (G : EtSh Λ (PV K gS)) :
    (pull (fibToP1 K gS s) Λ).obj ((pull (ιP gS s) Λ).obj G) ≅ (pull (fibι (qV K gS) s) Λ).obj G :=
  (pullCompIso Λ (fibToP1 K gS s) (ιP gS s)).symm.app G ≪≫ (pullCongr Λ (fibToP1_ιP gS s)).app G

/-- `e^* ιP^* G ⟶ ι^* G`. -/
def wG (G : EtSh Λ (PV K gS)) :
    (pull (fibToP1 K gS s) Λ).obj ((pull (ιP gS s) Λ).obj G) ⟶ (pull (fibι (qV K gS) s) Λ).obj G :=
  (wGIso gS s Λ G).hom

instance wG_isIso (G : EtSh Λ (PV K gS)) : IsIso (wG gS s Λ G) :=
  Iso.isIso_hom (wGIso gS s Λ G)

end TrG

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L8b =====
section

/-!
# S4-EtPBC-A, O2 L8b: `TrG` is onto and natural; `BCSurj 2` for `FGT` sheaves; killing degree-1 classes
* `TrG_surjective`, **`TrG_natural`** (`TrG G (x ∘ ιP^*m) = TrG H x ∘ ι^*m`);
* **`bcSurj_two_fgt`**: `BCSurj 2` for every `FGT` sheaf on `P¹_S` (`surjAt_coprod`, `bcSurj_two_free`, `bcSurj_two_of_epi`);
* `NT`, **`kill_lift`**: for `T` affine over `P¹_K`, every `κ ∈ Ext¹(Λ[T], ιP^*G)` is `κH ∘ ιP^*m` with `m : H ⟶ G`,
  `H` an `FGT` sheaf (`exists_kill` on `T`, `extFree_comp_mk₀`, the covariant exact sequence).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtCompact.GalTrE
  RamanujanPetersson.EtCompact.PushBC

universe u

section GenSurjG

universe w v₁ u₁ v₂ u₂

end GenSurjG

section TrG

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)] (Λ : Type) [CommRing Λ]

/-- `res_T ιP^* ≅ (T ⟶ P¹_K ⟶ P¹_S)^*`. -/
def NT (T : (P1 K).Etale) : pull (ιP gS s) Λ ⋙ res T.hom Λ ≅ pull (T.hom ≫ ιP gS s) Λ :=
  Functor.isoWhiskerLeft (pull (ιP gS s) Λ) (pullIsoRes T.hom Λ).symm ≪≫ (pullCompIso Λ T.hom (ιP gS s)).symm

end TrG

end RamanujanPetersson.EtPBC.EtMV

end

end


