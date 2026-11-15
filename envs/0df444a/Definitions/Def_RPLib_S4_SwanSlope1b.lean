-- Prove2me | Definitions.Def_RPLib_S4_SwanSlope1b
-- name    : RPLib_S4_SwanSlope1b
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T10:55:55.364519+00:00
-- url     : https://prove2.me/theorems/ca2f1c33-eb1f-41ce-9f87-a0415f6edaed
-- title:
--   Slope-one structure of wild inertia at infinity (cover level)
-- statement:
--   Let $C' \to C$ be a map of Galois covers of $\mathbb{F}_q(x)$, where $C$ has an Artin-Schreier generator $y$ with $y^q = y - g$ and $\deg g = 1$ (conductor one), and let $P'$ be a place over infinity of $C'$ with residue field $\mathbb{F}_q$. With $\Phi(\sigma) = a_\sigma$ the Artin-Schreier character, the file proves that $\Phi$ maps the upper ramification group $I^1$ at $P'$ onto $\mathbb{F}_q$ with kernel $I^{1+} = \bigcup_{v > 1} I^v$, so $$I^1 / I^{1+} \cong \mathbb{F}_q,$$ that every character of $I^1$ trivial on $I^{1+}$ is $\psi' \circ \Phi$ for an additive character $\psi'$, and that a representation $\rho$ with all breaks $\le 1$ at $P'$ has a twist $\rho \otimes \mathcal{L}_\psi(b\,g)$ with $\mathrm{Sw}_{P'} < \dim \rho$ (the local input of Katz's Fourier step).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (Swan conductors and wild ramification at infinity, used for Weil-type bounds of exponential sums). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Exponential Sums and Differential Equations, Annals of Mathematics Studies 124, Princeton University Press (1990), Section 7.8; N. M. Katz, Gauss Sums, Kloosterman Sums, and Monodromy Groups, Annals of Mathematics Studies 116, Princeton University Press (1988), Chapter 1

import Mathlib
import Definitions.Def_RPLib_S4_SwanSlope1a
import Definitions.Def_RPLib_S4_SwanGlobP
import Definitions.Def_RPLib_S4_SwanGlobASF1

/-!
# S4-Swan (K2), part 29: slope-1 local structure at `∞` (cover level)

Let `f : CoverHom C C'` be a morphism of covers with function fields `L ⊆ L'`, where `C` is an Artin-Schreier
cover of conductor `1` (`h : C.IsASGen Fq L y g 1`, e.g. `y^q - y = a x`), and let `Q'` be a place of `L'`
over `∞` of degree one (`|κ(Q')| ≤ q`). With `I' = I(Q')`, `U = I'^1` and `W = I'^{1+}` (the next lower
ramification group), the map `Φ = h.char ∘ f : I' → Fq` satisfies:

* `slope1_surj` / `slope1_upper`: `Φ(U) = Fq` and `Φ = 1` on `I'^v` for `v > 1` (Herbrand's theorem along `f`);
* `slope1_ker`: `ker (Φ|U) = W`, so `U/W ≅ Fq` (residue counting, `card_lower_quot_le`);
* `slope1_char`: every character of `U` trivial on `W` is `ψ' ∘ Φ`, i.e. the restriction of some `L_ψ'(g)`;
* `slope1_eigen` / `slope1_swan`: for a representation `ρ` of the cover group with all breaks `≤ 1` at `Q'`
  (`V ≠ 0`, `q` invertible, `ψ` primitive) there is `b ∈ Fq` with
  `Sw_{Q'}(ρ ⊗ L_{ψ(b·)}(g)) < dim V` (the local input of Katz's K11 step (4)).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open IsDedekindDomain Module

namespace RamanujanPetersson

namespace Swan

section Red

variable {S : Type*} [CommRing S] [IsDedekindDomain S] {L : Type*} [Field L] [Algebra S L]
  [IsFractionRing S L] (P : HeightOneSpectrum S)

open Classical in
/-- Reduction of `P`-integral elements to the residue ring `S / P`. -/
def resRed (x : L) : S ⧸ P.asIdeal :=
  if hx : 0 ≤ adicAdd P x then Ideal.Quotient.mk _ (exists_one_le_adicAdd_sub P hx).choose else 0

theorem resRed_spec {x : L} (hx : 0 ≤ adicAdd P x) :
    ∃ r : S, resRed P x = Ideal.Quotient.mk _ r ∧ 1 ≤ adicAdd P (x - algebraMap S L r) := by
  classical
  refine ⟨(exists_one_le_adicAdd_sub P hx).choose, ?_, (exists_one_le_adicAdd_sub P hx).choose_spec⟩
  unfold resRed
  rw [dif_pos hx]

/-- Integral elements with the same residue are congruent mod `P`. -/
theorem resRed_eq {x x' : L} (hx : 0 ≤ adicAdd P x) (hx' : 0 ≤ adicAdd P x')
    (h : resRed P x = resRed P x') : 1 ≤ adicAdd P (x - x') := by
  obtain ⟨r, hr, hr1⟩ := resRed_spec P hx
  obtain ⟨r', hr', hr1'⟩ := resRed_spec P hx'
  rw [hr, hr'] at h
  have h1 : r - r' ∈ P.asIdeal := Ideal.Quotient.eq.1 h
  have h2 := (one_le_adicAdd_algebraMap_iff (L := L) P (r - r')).2 h1
  have h3 : x - x' = ((x - algebraMap S L r) - (x' - algebraMap S L r')) + algebraMap S L (r - r') := by
    rw [map_sub]; ring
  rw [h3]
  refine le_trans ?_ (AddValuation.map_add _ _ _)
  exact le_min (le_trans (le_min hr1 hr1') (AddValuation.map_sub _ _ _)) h2

end Red

end Swan

namespace GalCover

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin
  GalCover.grp GalCover.fG GalCover.act GalCover.gal

section Slope1

variable {A : Type} [CommRing A] [IsDomain A] {C C' : GalCover A} (f : CoverHom C C')
variable (Fq : Type) [Field Fq] [DecidableEq (RatFunc Fq)] [Algebra A (RatFunc Fq)]
  [IsFractionRing A (RatFunc Fq)]
variable {L : Type} [Field L] [Algebra C.B L] [IsFractionRing C.B L] [Algebra (RatFunc Fq) L]
  [Algebra A L] [IsScalarTower A (RatFunc Fq) L] [IsScalarTower A C.B L] [MulSemiringAction C.G L]
  [SMulDistribClass C.G C.B L]
variable {L' : Type} [Field L'] [Algebra C'.B L'] [IsFractionRing C'.B L'] [Algebra (RatFunc Fq) L']
  [Algebra A L'] [IsScalarTower A (RatFunc Fq) L'] [IsScalarTower A C'.B L'] [MulSemiringAction C'.G L']
  [SMulDistribClass C'.G C'.B L'] [Algebra L L'] [IsScalarTower (RatFunc Fq) L L']
variable (hf : ∀ b : C.B, algebraMap L L' (algebraMap C.B L b) = algebraMap C'.B L' (f.ringHom b))

attribute [local instance] infChartAlg infChartAction infChart_isGaloisGroup infChart_faithfulSMul
  infChart_faithfulSMul' infChart_isScalarTower infChart_isScalarTower' infChart_isIntegral

variable [FiniteDimensional (RatFunc Fq) L] [Algebra.IsSeparable (RatFunc Fq) L]
  [FiniteDimensional (RatFunc Fq) L'] [Algebra.IsSeparable (RatFunc Fq) L'] [Fintype Fq]

attribute [local instance] infChart_finite'

variable {y : L} {g : RatFunc Fq} (h : C.IsASGen Fq L y g 1) (Q' : HeightOneSpectrum (infChart Fq L'))

variable (C') in
/-- The slope-one group `U = I'^1` at `Q'`. -/
abbrev s1U : Subgroup (C'.infInertia Fq L' Q'.asIdeal) := (C'.infRamFn Fq L' Q').upper 1

variable (C') in
/-- The group `W = I'^{1+}`: the lower ramification group after `I'^1`. -/
abbrev s1W : Subgroup (C'.infInertia Fq L' Q'.asIdeal) :=
  (C'.infRamFn Fq L' Q').lower ((C'.infRamFn Fq L' Q').upperIdx 1 + 1)

/-- The Artin-Schreier map `Φ = h.char ∘ f` on the inertia at `Q'`. -/
def s1Phi : C'.infInertia Fq L' Q'.asIdeal →* Multiplicative Fq :=
  (h.char.comp f.grpHom).comp (C'.infInertia Fq L' Q'.asIdeal).subtype

theorem s1Phi_apply (σ : C'.infInertia Fq L' Q'.asIdeal) :
    s1Phi f Fq h Q' σ = Multiplicative.ofAdd (h.val (f.grpHom σ)) := rfl

variable (C') in
theorem s1W_le_s1U : s1W C' Fq Q' ≤ s1U C' Fq Q' :=
  (C'.infRamFn Fq L' Q').lower_antitone (Nat.le_succ _)

include hf in
/-- `Φ` maps `I'^1` onto `Fq` (Herbrand: `I'^1` maps onto `I(Q' ∩ L)^1 = I(Q' ∩ L) = G`). -/
theorem slope1_surj (c : Fq) : ∃ σ ∈ s1U C' Fq Q', s1Phi f Fq h Q' σ = Multiplicative.ofAdd c := by
  classical
  have : Fintype (infInertiaRes f Fq hf Q').ker := Fintype.ofFinite _
  have hT : ((C'.infRamFn Fq L' Q').upper 1).map (infInertiaRes f Fq hf Q') =
      (C.infRamFn Fq L (underInf Fq L L' Q')).upper 1 := (infTower f Fq hf Q').map_upper 1
  have hU : (C.infRamFn Fq L (underInf Fq L L' Q')).upper 1 = ⊤ :=
    (h.constI (underInf Fq L L' Q')).upper_of_le (by norm_num)
  obtain ⟨σ0, hσ0⟩ := (h.val_bijective (underInf Fq L L' Q')).2 c
  have hσ0I : σ0 ∈ C.infInertia Fq L (underInf Fq L L' Q').asIdeal := by
    rw [h.inertia_eq_top]; exact Subgroup.mem_top _
  have hmem : (⟨σ0, hσ0I⟩ : C.infInertia Fq L (underInf Fq L L' Q').asIdeal) ∈
      ((C'.infRamFn Fq L' Q').upper 1).map (infInertiaRes f Fq hf Q') := by
    rw [hT, hU]; exact Subgroup.mem_top _
  obtain ⟨τ, hτ, hτeq⟩ := Subgroup.mem_map.1 hmem
  refine ⟨τ, hτ, ?_⟩
  have h1 : f.grpHom τ = σ0 := congrArg Subtype.val hτeq
  rw [s1Phi_apply, h1, hσ0]

include hf in
/-- `Φ` is trivial on `I'^v` for `v > 1` (Herbrand: `I(Q' ∩ L)^v = 1` for `v > 1`). -/
theorem slope1_upper {v : ℚ} (hv : 1 < v) {σ : C'.infInertia Fq L' Q'.asIdeal}
    (hσ : σ ∈ (C'.infRamFn Fq L' Q').upper v) : s1Phi f Fq h Q' σ = 1 := by
  classical
  have : Fintype (infInertiaRes f Fq hf Q').ker := Fintype.ofFinite _
  have hT : ((C'.infRamFn Fq L' Q').upper v).map (infInertiaRes f Fq hf Q') =
      (C.infRamFn Fq L (underInf Fq L L' Q')).upper v := (infTower f Fq hf Q').map_upper v
  rw [(h.constI (underInf Fq L L' Q')).upper_of_lt (by exact_mod_cast hv)] at hT
  have hm : infInertiaRes f Fq hf Q' σ ∈ (⊥ : Subgroup (C.infInertia Fq L (underInf Fq L L' Q').asIdeal)) :=
    hT ▸ Subgroup.mem_map_of_mem _ hσ
  rw [Subgroup.mem_bot] at hm
  have h1 : f.grpHom σ = 1 := congrArg Subtype.val hm
  rw [s1Phi_apply, h1, h.val_one]
  rfl

variable (C') in
theorem one_lt_phi_s1 :
    1 < (C'.infRamFn Fq L' Q').phi ((C'.infRamFn Fq L' Q').upperIdx 1 + 1) :=
  lt_of_le_of_lt (C'.infRamFn Fq L' Q').phi_upperIdx_one.2 ((C'.infRamFn Fq L' Q').phi_lt_succ _)

variable (C') in
theorem s1W_eq_upper :
    s1W C' Fq Q' = (C'.infRamFn Fq L' Q').upper
      ((C'.infRamFn Fq L' Q').phi ((C'.infRamFn Fq L' Q').upperIdx 1 + 1)) :=
  ((C'.infRamFn Fq L' Q').upper_phi _).symm

include hf in
theorem slope1_W {σ : C'.infInertia Fq L' Q'.asIdeal} (hσ : σ ∈ s1W C' Fq Q') : s1Phi f Fq h Q' σ = 1 :=
  slope1_upper f Fq hf h Q' (one_lt_phi_s1 C' Fq Q') (by rw [← s1W_eq_upper]; exact hσ)

variable (C') in
/-- Residue counting: `|I'^1 / I'^{1+}| ≤ |κ(Q')| ≤ q`. -/
theorem slope1_card (hdeg : Nat.card (infChart Fq L' ⧸ Q'.asIdeal) ≤ Nat.card Fq) :
    Nat.card (s1U C' Fq Q' ⧸ (s1W C' Fq Q').subgroupOf (s1U C' Fq Q')) ≤ Nat.card Fq :=
  le_trans ((C'.infLocData Fq L' Q').card_lower_quot_le (Swan.resRed Q')
    (fun _ _ hx hx' hxx' => Swan.resRed_eq Q' hx hx' hxx') _) hdeg

include hf in
/-- **Slope one, kernel**: an element of `I'^1` with `Φ σ = 0` lies in `I'^{1+}`; so `I'^1/I'^{1+} ≅ Fq`. -/
theorem slope1_ker (hdeg : Nat.card (infChart Fq L' ⧸ Q'.asIdeal) ≤ Nat.card Fq)
    {σ : C'.infInertia Fq L' Q'.asIdeal} (hσU : σ ∈ s1U C' Fq Q') (hσ : s1Phi f Fq h Q' σ = 1) :
    σ ∈ s1W C' Fq Q' :=
  Swan.mem_of_map_eq_one (s1Phi f Fq h Q') (s1W_le_s1U C' Fq Q') (slope1_surj f Fq hf h Q')
    (fun _ hσ => slope1_W f Fq hf h Q' hσ) (slope1_card C' Fq Q' hdeg) hσU hσ

include hf in
/-- **Slope one, characters**: every character of `I'^1` trivial on `I'^{1+}` is `ψ' ∘ Φ`. -/
theorem slope1_char (hdeg : Nat.card (infChart Fq L' ⧸ Q'.asIdeal) ≤ Nat.card Fq) {k : Type} [Field k]
    (χ : C'.infInertia Fq L' Q'.asIdeal →* kˣ) (hχ : ∀ σ ∈ s1W C' Fq Q', χ σ = 1) :
    ∃ ψ' : AddChar Fq k, ∀ σ ∈ s1U C' Fq Q', ((χ σ : kˣ) : k) = ψ' (h.val (f.grpHom σ)) :=
  Swan.exists_addChar_eq (s1Phi f Fq h Q') (s1W_le_s1U C' Fq Q') (slope1_surj f Fq hf h Q')
    (fun _ hσ => slope1_W f Fq hf h Q' hσ) (slope1_card C' Fq Q' hdeg) χ hχ

section Rep

variable {k V : Type} [Field k] [AddCommGroup V] [Module k V] (ρ : Representation k C'.G V)

variable (C') in
theorem s1W_trivial (hB : (C'.infRamFn Fq L' Q').BrkLE (ρ.comp (C'.infInertia Fq L' Q'.asIdeal).subtype) 1) :
    ∀ σ ∈ s1W C' Fq Q', ∀ w : V, (ρ.comp (C'.infInertia Fq L' Q'.asIdeal).subtype) σ w = w := by
  intro σ hσ w
  have h1 := hB _ (one_lt_phi_s1 C' Fq Q')
  rw [← s1W_eq_upper] at h1
  exact (Swan.mem_fixd _).1 (h1 ▸ Submodule.mem_top) σ hσ

include hf in
/-- **Slope one, eigenvector**: a common eigenvector of `I'^1` with eigencharacter `ψ(a Φ)`. -/
theorem slope1_eigen (hdeg : Nat.card (infChart Fq L' ⧸ Q'.asIdeal) ≤ Nat.card Fq) [Nontrivial V]
    (hB : (C'.infRamFn Fq L' Q').BrkLE (ρ.comp (C'.infInertia Fq L' Q'.asIdeal).subtype) 1)
    (ψ : AddChar Fq k) (hψ : ψ.IsPrimitive) (hq : (Fintype.card Fq : k) ≠ 0) :
    ∃ a : Fq, ∃ w : V, w ≠ 0 ∧ ∀ σ ∈ s1U C' Fq Q', ρ σ w = ψ (a * h.val (f.grpHom σ)) • w :=
  Swan.exists_eigen (s1Phi f Fq h Q') (s1W_le_s1U C' Fq Q') (slope1_surj f Fq hf h Q')
    (fun _ hσ => slope1_W f Fq hf h Q' hσ) (slope1_card C' Fq Q' hdeg) _ (s1W_trivial C' Fq Q' ρ hB) ψ hψ hq

include hf in
/-- The twist `ρ ⊗ L_{ψ'}(g)` still has all breaks `≤ 1` at `Q'`. -/
theorem slope1_brkLE_twist
    (hB : (C'.infRamFn Fq L' Q').BrkLE (ρ.comp (C'.infInertia Fq L' Q'.asIdeal).subtype) 1)
    (ψ' : AddChar Fq k) :
    (C'.infRamFn Fq L' Q').BrkLE
      ((Swan.twist ρ ((h.lpsi ψ').comp f.grpHom)).comp (C'.infInertia Fq L' Q'.asIdeal).subtype) 1 := by
  intro v hv
  rw [eq_top_iff]
  intro w _
  rw [Swan.mem_fixd]
  intro σ hσ
  have hρσ : (ρ.comp (C'.infInertia Fq L' Q'.asIdeal).subtype) σ w = w :=
    (Swan.mem_fixd _).1 (hB v hv ▸ Submodule.mem_top) σ hσ
  have hχ := slope1_upper f Fq hf h Q' hv hσ
  rw [s1Phi_apply] at hχ
  have hval : h.val (f.grpHom σ) = 0 := by
    have := congrArg Multiplicative.toAdd hχ
    simpa using this
  show (((h.lpsi ψ' (f.grpHom σ) : kˣ) : k)) • (ρ σ w) = w
  rw [h.lpsi_apply, hval, AddChar.map_zero_eq_one, one_smul]
  exact hρσ

include hf in
/-- **Slope one, Swan (K11 step (4) local input)**: if `ρ` has all breaks `≤ 1` at `Q'` (`V ≠ 0`, `q`
invertible in `k`, `ψ` primitive), then `Sw_{Q'}(ρ ⊗ L_{ψ(b·)}(g)) < dim V` for some `b ∈ Fq`. -/
theorem slope1_swan [FiniteDimensional k V] (hdeg : Nat.card (infChart Fq L' ⧸ Q'.asIdeal) ≤ Nat.card Fq)
    [Nontrivial V] (hB : (C'.infRamFn Fq L' Q').BrkLE (ρ.comp (C'.infInertia Fq L' Q'.asIdeal).subtype) 1)
    (ψ : AddChar Fq k) (hψ : ψ.IsPrimitive) (hq : (Fintype.card Fq : k) ≠ 0) :
    ∃ b : Fq, C'.swanInf Fq L' (Swan.twist ρ ((h.lpsi (ψ.mulShift b)).comp f.grpHom)) Q' < finrank k V := by
  obtain ⟨b, hb⟩ := Swan.exists_fixd_twist_ne_bot (s1Phi f Fq h Q') (s1W_le_s1U C' Fq Q')
    (slope1_surj f Fq hf h Q') (fun _ hσ => slope1_W f Fq hf h Q' hσ) (slope1_card C' Fq Q' hdeg) _
    (s1W_trivial C' Fq Q' ρ hB) ψ hψ hq
  refine ⟨b, ?_⟩
  exact (C'.infRamFn Fq L' Q').swan_lt_of_fixd _ (slope1_brkLE_twist f Fq hf h Q' ρ hB _) hb

end Rep

end Slope1

end GalCover

end RamanujanPetersson


