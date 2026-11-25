-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_111
-- name    : RPLib_FX_EtPBC_111
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T22:19:53.690117+00:00
-- url     : https://prove2.me/theorems/82100ea5-08e4-5faf-9fab-2212caad9825
-- title:
--   Proper base change for the projective line, library file 111
-- statement:
--   File 111 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovFil2`: S4-EtPBC-A, R4-T2 (A2c-1e): the `p`-adic filtration on sections of `O(d)` is the `p`-power filtration
--   * `S4.Def_RP_EtPBC_A_CovLim4`: S4-EtPBC-A, R4-T2 (A2c-2d): compatible families are combinations with coefficients in a `p`-precomplete ring
--   * `S4.Def_RP_EtPBC_A_CovHat6`: S4-EtPBC-A, R4-T2 (A2c-3f): the level reductions of the completed charts are surjective
--   * `S4.Def_RP_EtPBC_A_CovGl2`: S4-EtPBC-A, R4-T2 (G1c, part 2b): gluing finite etale chart algebras over `Y_{V'}`
--   * `S4.Def_RP_EtPBC_A_SecCoc`: S4-EtPBC-A, L1c (part 1): cocycles of `I^•(W)` as `Ext` classes
--   * `S4.Def_RP_EtPBC_A_StkBC`: S4-EtPBC-A, L1f: the base change map on stalks
--   * `S4.Def_RP_EtPBC_A_Inj0c`: S4-EtPBC-A, G1c: base change is injective on germs in degree `0` (universally closed `g`)
--   * `S4.Def_RP_EtPBC_A_Inj0dg`: S4-EtPBC-A, G1d part 1b: the point `v` lies in `good`, and the lifted point `goodPt`
--   * `S4.Def_RP_EtPBC_A_FBCv`: S4-EtPBC-A, R4 (FBC-c, part 1): sections of a constant sheaf with prescribed values on a finite fibre
--   * `S4.Def_RP_EtPBC_A_DescG5`: S4-EtPBC-A, R4-T1d (part 2): the sheets cover `U₀`, the descended section `σ`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_089
import Definitions.Def_RPLib_FX_EtPBC_091
import Definitions.Def_RPLib_FX_EtPBC_099

/-!
# Proper base change for the projective line, library file 111

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovFil2`: S4-EtPBC-A, R4-T2 (A2c-1e): the `p`-adic filtration on sections of `O(d)` is the `p`-power filtration
* `S4.Def_RP_EtPBC_A_CovLim4`: S4-EtPBC-A, R4-T2 (A2c-2d): compatible families are combinations with coefficients in a `p`-precomplete ring
* `S4.Def_RP_EtPBC_A_CovHat6`: S4-EtPBC-A, R4-T2 (A2c-3f): the level reductions of the completed charts are surjective
* `S4.Def_RP_EtPBC_A_CovGl2`: S4-EtPBC-A, R4-T2 (G1c, part 2b): gluing finite etale chart algebras over `Y_{V'}`
* `S4.Def_RP_EtPBC_A_SecCoc`: S4-EtPBC-A, L1c (part 1): cocycles of `I^•(W)` as `Ext` classes
* `S4.Def_RP_EtPBC_A_StkBC`: S4-EtPBC-A, L1f: the base change map on stalks
* `S4.Def_RP_EtPBC_A_Inj0c`: S4-EtPBC-A, G1c: base change is injective on germs in degree `0` (universally closed `g`)
* `S4.Def_RP_EtPBC_A_Inj0dg`: S4-EtPBC-A, G1d part 1b: the point `v` lies in `good`, and the lifted point `goodPt`
* `S4.Def_RP_EtPBC_A_FBCv`: S4-EtPBC-A, R4 (FBC-c, part 1): sections of a constant sheaf with prescribed values on a finite fibre
* `S4.Def_RP_EtPBC_A_DescG5`: S4-EtPBC-A, R4-T1d (part 2): the sheets cover `U₀`, the descended section `σ`
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_CovFil2 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-1e): the `p`-adic filtration on sections of `O(d)` is the `p`-power filtration

* `FilProp`: every section of `O(d)` with entries in `p^(j+1)` is `∑ αᵢ yᵢ` with `yᵢ` sections with entries in `p^j`;
* `fil_step`: `FilProp` at one level `k` for `d ≥ d₀ + F` (from uniform `H¹` vanishing and uniform relations);
* **`fil_tower`**: one `d₂` with `FilProp` at every level of the tower and every `d ≥ d₂`.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Lv

end Lv

section Tower

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] (φ₀ : B₀ →+* N)
  (φ₁ : B₁ →+* N) (J₀ : Ideal B₀) (J₁ : Ideal B₁) (JN : Ideal N) (h₀ : J₀.map φ₀ = JN) (h₁ : J₁.map φ₁ = JN)
  (t₀ : B₀) (t₁ : B₁) (hφ₀ : IsAwayMap φ₀ t₀) (hφ₁ : IsAwayMap φ₁ t₁) (hu₀ : IsUnit (φ₀ t₀))
  (hu₁ : IsUnit (φ₁ t₁)) (C₀ : LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ 0) (ιB₀ : R →+* B₀) (ιB₁ : R →+* B₁)
  (p : Ideal R)

include hφ₀ hφ₁ hu₀ hu₁

/-- **The `p`-adic filtration is the `p`-power filtration** at every level of the tower, for `d ≥ d₂`. -/
theorem fil_tower [IsNoetherianRing R] [IsNoetherianRing B₀] {g : ℕ} (α : Fin g → R)
    (hα : p = Ideal.span (Set.range α)) (hts : φ₀ t₀ * φ₁ t₁ = 1) (hB : (eval₂RingHom ιB₀ t₀).Finite)
    (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) :
    ∃ d₂ : ℕ, ∀ d, d₂ ≤ d → ∀ k,
      FilProp ιB₀ ιB₁ p α (tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ k) d := by
  obtain ⟨F, hrel⟩ := relV_uniform p α φ₀ φ₁ t₀ t₁ ιB₀ ιB₁ hφ₁ hu₁ hts hιB
  obtain ⟨d₀, hd₀⟩ := spl_tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ ιB₀ ιB₁ p hts hB hιB hJ₀
  exact ⟨d₀ + F, fun d hd k => fil_step ιB₀ ιB₁ p α hα hts hιB hJ₀ hJ₁ _ d d₀ F hd
    (fun d' hd' n z hz => hd₀ d' hd' k n z hz) hrel⟩

end Tower

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovLim4 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-2d): compatible families are combinations with coefficients in a `p`-precomplete ring

For compatible families `σ : Fin r → Gam C H d` generating level `0`, over `R` with `IsPrecomplete p R`:
* `gam_agree`: two compatible families that agree at level `k` agree at every level `m ≤ k`;
* `gam_seq`: a level-`k₀` combination extends to a combination at all levels with congruent coefficients;
* **`gam_gen`**: every compatible family is `∑ aᵢ σᵢ` at all levels;
* **`gam_ker`**: a compatible family vanishing at level `k` is `∑ aᵢ σᵢ` with all `aᵢ ∈ p^(k+1)`;
* `gen_all`: every level-`m` section is a combination of the `σᵢ`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Agree

end Agree

section Lim

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k)) (ιB₀ : R →+* B₀)
  (ιB₁ : R →+* B₁) (p : Ideal R) {r : ℕ} (σ : Fin r → (∀ k, (C k).E₀) × (∀ k, (C k).E₁)) {g : ℕ}
  (α : Fin g → R)

/-- **Extension of a level-`k₀` combination** to all levels, with coefficients congruent modulo `p^(k₀+1)`. -/
theorem gam_seq [IsPrecomplete p R] (hα : ∀ i, α i ∈ p) (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁)
    (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) {d : ℕ} (hσ : ∀ i, σ i ∈ Gam C H d)
    (hgen0 : ∀ y ∈ (C 0).sec d, ∃ c, y = lev C ιB₀ ιB₁ σ 0 c) (hfil : ∀ k, FilProp ιB₀ ιB₁ p α (C k) d)
    {x : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (hx : x ∈ Gam C H d) (k₀ : ℕ) (b₀ : Fin r → R)
    (hb₀ : (x.1 k₀, x.2 k₀) = lev C ιB₀ ιB₁ σ k₀ b₀) :
    ∃ b : Fin r → R, (∀ i, b i - b₀ i ∈ p ^ (k₀ + 1)) ∧ ∀ m, (x.1 m, x.2 m) = lev C ιB₀ ιB₁ σ m b := by
  have hstep : ∀ (n : ℕ) (a : Fin r → R), ((x.1 (k₀ + n), x.2 (k₀ + n)) = lev C ιB₀ ιB₁ σ (k₀ + n) a ∧
      ∀ i, a i - b₀ i ∈ p ^ (k₀ + 1)) →
      ∃ a' : Fin r → R, ((x.1 (k₀ + n + 1), x.2 (k₀ + n + 1)) = lev C ιB₀ ιB₁ σ (k₀ + n + 1) a' ∧
        ∀ i, a' i - b₀ i ∈ p ^ (k₀ + 1)) ∧ ∀ i, a' i - a i ∈ p ^ (k₀ + n + 1) := by
    intro n a ⟨ha, ha'⟩
    have hl := (mem_gam C H x).1 hx (k₀ + n)
    have hl' := (mem_gam C H x).1 hx (k₀ + n + 1)
    obtain ⟨y, hy⟩ : ∃ y : (C (k₀ + n + 1)).E₀ × (C (k₀ + n + 1)).E₁,
        y = (x.1 (k₀ + n + 1), x.2 (k₀ + n + 1)) - lev C ιB₀ ιB₁ σ (k₀ + n + 1) a := ⟨_, rfl⟩
    have hys : y ∈ (C (k₀ + n + 1)).sec d := by
      rw [hy]
      exact AddSubgroup.sub_mem _ (((C (k₀ + n + 1)).mem_sec d _).2 hl'.2.2)
        (lev_mem C H ιB₀ ιB₁ σ hιB hσ _ a)
    have ha₀ : (lev C ιB₀ ιB₁ σ (k₀ + n) a).1 = x.1 (k₀ + n) := (congrArg Prod.fst ha).symm
    have ha₁ : (lev C ιB₀ ιB₁ σ (k₀ + n) a).2 = x.2 (k₀ + n) := (congrArg Prod.snd ha).symm
    have hy₀ : y.1 ∈ (p ^ (k₀ + n + 1)).map (lι₀ ιB₀ (C (k₀ + n + 1))) := by
      rw [← ker_ρ₀ ιB₀ p (H (k₀ + n)) hJ₀, RingHom.mem_ker, hy, Prod.fst_sub, map_sub,
        lev_ρ₀ C H ιB₀ ιB₁ σ hσ, ha₀]
      exact sub_eq_zero.2 hl.1
    have hy₁ : y.2 ∈ (p ^ (k₀ + n + 1)).map (lι₁ ιB₁ (C (k₀ + n + 1))) := by
      rw [← ker_ρ₁ ιB₁ p (H (k₀ + n)) hJ₁, RingHom.mem_ker, hy, Prod.snd_sub, map_sub,
        lev_ρ₁ C H ιB₀ ιB₁ σ hσ, ha₁]
      exact sub_eq_zero.2 hl.2.1
    obtain ⟨b, hb, hbe⟩ := gen_lev C H ιB₀ ιB₁ p σ α hα hιB hJ₀ hJ₁ hσ hgen0 hfil (k₀ + n + 1)
      (k₀ + n + 1) y hys hy₀ hy₁
    refine ⟨a + b, ⟨?_, fun i => ?_⟩, fun i => ?_⟩
    · rw [lev_add, ← hbe, hy, add_sub_cancel]
    · rw [Pi.add_apply, show a i + b i - b₀ i = (a i - b₀ i) + b i by ring]
      exact Ideal.add_mem _ (ha' i) (Ideal.pow_le_pow_right (by omega) (hb i))
    · rw [Pi.add_apply, add_sub_cancel_left]
      exact hb i
  obtain ⟨f, hf⟩ := seq_choice
    (fun n a => (x.1 (k₀ + n), x.2 (k₀ + n)) = lev C ιB₀ ιB₁ σ (k₀ + n) a ∧ ∀ i, a i - b₀ i ∈ p ^ (k₀ + 1))
    (fun n a a' => ∀ i, a' i - a i ∈ p ^ (k₀ + n + 1)) ⟨b₀, hb₀, fun i => by simp⟩ hstep
  have hcau : ∀ n t i, f (n + t) i - f n i ∈ p ^ (k₀ + n + 1) := by
    intro n t
    induction t with
    | zero => intro i; simp
    | succ t ih =>
      intro i
      have h := Ideal.add_mem _ (Ideal.pow_le_pow_right (by omega : k₀ + n + 1 ≤ k₀ + (n + t) + 1)
        ((hf (n + t)).2 i)) (ih i)
      rw [sub_add_sub_cancel] at h
      exact h
  have hL : ∀ i, ∃ L : R, ∀ n, f n i - L ∈ p ^ n := by
    intro i
    have hc : ∀ {m n : ℕ}, m ≤ n → f m i ≡ f n i [SMOD (p ^ m • ⊤ : Submodule R R)] := by
      intro m n hmn
      rw [SModEq.sub_mem, ideal_pow_smul_top]
      obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hmn
      have h := Submodule.neg_mem _ (hcau m t i)
      rw [neg_sub] at h
      exact Ideal.pow_le_pow_right (by omega) h
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (f := fun n => f n i) (inferInstance : IsPrecomplete p R) @hc
    refine ⟨L, fun n => ?_⟩
    have h := SModEq.sub_mem.1 (hL n)
    rwa [ideal_pow_smul_top] at h
  choose L hL using hL
  have hN : ∀ n, (x.1 (k₀ + n), x.2 (k₀ + n)) = lev C ιB₀ ιB₁ σ (k₀ + n) L := by
    intro n
    rw [(hf n).1.1]
    refine lev_congr C ιB₀ ιB₁ p σ hJ₀ hJ₁ (k₀ + n) fun i => ?_
    have h1 := hcau n (k₀ + 1) i
    have h2 := hL i (n + (k₀ + 1))
    rw [show n + (k₀ + 1) = k₀ + n + 1 by omega] at h1 h2
    have h := Submodule.sub_mem _ h2 h1
    rwa [sub_sub_sub_cancel_left] at h
  refine ⟨L, fun i => ?_, fun m => ?_⟩
  · have h := Submodule.sub_mem _ ((hf (k₀ + 1)).1.2 i) (hL i (k₀ + 1))
    rwa [sub_sub_sub_cancel_left] at h
  · have h := gam_agree C H hx (levF_mem C H ιB₀ ιB₁ σ hιB hσ L) (k₀ + m) m (by omega)
      (congrArg Prod.fst (hN m)) (congrArg Prod.snd (hN m))
    exact Prod.ext h.1 h.2

/-- **Every compatible family is a combination of the `σᵢ`** at all levels. -/
theorem gam_gen [IsPrecomplete p R] (hα : ∀ i, α i ∈ p) (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁)
    (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) {d : ℕ} (hσ : ∀ i, σ i ∈ Gam C H d)
    (hgen0 : ∀ y ∈ (C 0).sec d, ∃ c, y = lev C ιB₀ ιB₁ σ 0 c) (hfil : ∀ k, FilProp ιB₀ ιB₁ p α (C k) d)
    {x : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (hx : x ∈ Gam C H d) :
    ∃ a : Fin r → R, ∀ m, (x.1 m, x.2 m) = lev C ιB₀ ιB₁ σ m a := by
  have h0 : (x.1 0, x.2 0) ∈ (C 0).sec d := ((C 0).mem_sec d _).2 ((mem_gam C H x).1 hx 0).2.2
  have htop₀ : (x.1 0, x.2 0).1 ∈ (p ^ 0).map (lι₀ ιB₀ (C 0)) := by
    rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]
    exact Submodule.mem_top
  have htop₁ : (x.1 0, x.2 0).2 ∈ (p ^ 0).map (lι₁ ιB₁ (C 0)) := by
    rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]
    exact Submodule.mem_top
  obtain ⟨b₀, -, hb₀⟩ := gen_lev C H ιB₀ ιB₁ p σ α hα hιB hJ₀ hJ₁ hσ hgen0 hfil 0 0 _ h0 htop₀ htop₁
  obtain ⟨b, -, hb⟩ := gam_seq C H ιB₀ ιB₁ p σ α hα hιB hJ₀ hJ₁ hσ hgen0 hfil hx 0 b₀ hb₀
  exact ⟨b, hb⟩

/-- **A compatible family vanishing at level `k`** is a combination with coefficients in `p^(k+1)`. -/
theorem gam_ker [IsPrecomplete p R] (hα : ∀ i, α i ∈ p) (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁)
    (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) {d : ℕ} (hσ : ∀ i, σ i ∈ Gam C H d)
    (hgen0 : ∀ y ∈ (C 0).sec d, ∃ c, y = lev C ιB₀ ιB₁ σ 0 c) (hfil : ∀ k, FilProp ιB₀ ιB₁ p α (C k) d)
    {x : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (hx : x ∈ Gam C H d) (k : ℕ) (hk₀ : x.1 k = 0)
    (hk₁ : x.2 k = 0) :
    ∃ a : Fin r → R, (∀ i, a i ∈ p ^ (k + 1)) ∧ ∀ m, (x.1 m, x.2 m) = lev C ιB₀ ιB₁ σ m a := by
  have hb₀ : (x.1 k, x.2 k) = lev C ιB₀ ιB₁ σ k 0 := by
    rw [lev_zero]
    exact Prod.ext hk₀ hk₁
  obtain ⟨b, hb, hb'⟩ := gam_seq C H ιB₀ ιB₁ p σ α hα hιB hJ₀ hJ₁ hσ hgen0 hfil hx k 0 hb₀
  exact ⟨b, fun i => by simpa using hb i, hb'⟩

end Lim

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovHat6 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-3f): the level reductions of the completed charts are surjective

* **`θ₀ k : hE₀ →+* E₀(k)`**, **`θ₁ k : hE₁ →+* E₁(k)`** (evaluation of the first, resp. second, coordinate);
  `θ₀_frac₀`, `θ₁_frac₁`, `ρ₀_θ₀`, `ρ₁_θ₁` (compatible with the transitions), `θ₀_β₀`, `θ₁_β₁`;
* **`gen_sys`**: lifts of level-`0` generators of `O(d)`; **`gam_lev_surj`**: every level-`m` section of `O(d)` is
  the level-`m` part of a compatible family;
* **`θ₀_surj`**, **`θ₁_surj`** (all `k`), when the transitions are surjective on sections and `FilProp` holds in all
  degrees `≥ D`.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Theta

end Theta

section Surj

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k)) (ιB₀ : R →+* B₀)
  (ιB₁ : R →+* B₁) (p : Ideal R) (hts : φ₀ t₀ * φ₁ t₁ = 1)

include hts in
/-- **Level surjectivity**: every level-`m` section of `O(d)` comes from a compatible family. -/
theorem gam_lev_surj [IsNoetherianRing R] {g : ℕ} (α : Fin g → R) (hα : ∀ i, α i ∈ p)
    (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hB₀ : (eval₂RingHom ιB₀ t₀).Finite) (hB₁ : (eval₂RingHom ιB₁ t₁).Finite)
    (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) {d : ℕ}
    (hs : ∀ k, Function.Surjective ((H k).secMap (Ideal.Quotient.factor_mk _ _) d))
    (hfil : ∀ k, FilProp ιB₀ ιB₁ p α (C k) d) (m : ℕ) (y : (C m).E₀ × (C m).E₁) (hy : y ∈ (C m).sec d) :
    ∃ x ∈ Gam C H d, x.1 m = y.1 ∧ x.2 m = y.2 := by
  obtain ⟨r, σ, hσ, hgen0⟩ := gen_sys C H ιB₀ ιB₁ hts hιB hB₀ hB₁ hs
  obtain ⟨c, hc⟩ := gen_all C H ιB₀ ιB₁ p σ α hα hιB hJ₀ hJ₁ hσ hgen0 hfil m y hy
  exact ⟨levF C ιB₀ ιB₁ σ c, levF_mem C H ιB₀ ιB₁ σ hιB hσ c, (congrArg Prod.fst hc).symm,
    (congrArg Prod.snd hc).symm⟩

end Surj

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovGl2 =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1c, part 2b): gluing finite etale chart algebras over `Y_{V'}`

Chart algebras `E₀`, `E₁`, `E₀₁` over `R' ⊗ Γ(Y₀)`, `R' ⊗ Γ(Y₁)`, `R' ⊗ Γ(Y₀₁)`, glued by localizations `ψ₀`, `ψ₁` (the
data of `CoverLift`), give a relative gluing datum **`glD`** over the chart cover `covV`; its glued scheme maps to
`Y_{V'}` by **`toBase`**, which is finite and etale when `E₀`, `E₁` are.
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
  (π : Y ⟶ PV K gV)

theorem unit0 : IsUnit (φ0V K gV π (algebraMap (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 0) Polynomial.X)) := by
  show IsUnit (φY0 K gV π (algebraMap (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 0) Polynomial.X))
  rw [(φY0 K gV π).commutes]
  exact IsUnit.of_mul_eq_one _ (hts_Y K gV π)

variable [IsAffine V] [IsFinite π] (R' : Type u) [CommRing R'] [Algebra Γ(V, ⊤) R'] {E₀ E₁ E₀₁ : Type u}
  [CommRing E₀] [CommRing E₁] [CommRing E₀₁] [Algebra (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0)) E₀]
  [Algebra (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 1)) E₁] [Algebra (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1)) E₀₁]
  (ψ₀ : E₀ →+* E₀₁) (ψ₁ : E₁ →+* E₀₁)
  (hψ₀ : ∀ (r : R') (b : Γ(Y, Yc K gV π 0)), ψ₀ (algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0)) E₀ (r ⊗ₜ b)) =
    algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1)) E₀₁ (r ⊗ₜ φY0 K gV π b))
  (hψ₁ : ∀ (r : R') (b : Γ(Y, Yc K gV π 1)), ψ₁ (algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 1)) E₁ (r ⊗ₜ b)) =
    algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1)) E₀₁ (r ⊗ₜ φY1 K gV π b))
  (aw₀ : IsAwayMap ψ₀ (algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0)) E₀
    ((1 : R') ⊗ₜ algebraMap (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 0) Polynomial.X)))
  (aw₁ : IsAwayMap ψ₁ (algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 1)) E₁
    ((1 : R') ⊗ₜ algebraMap (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 1) Polynomial.X)))

/-- The structure maps `Spec Eⱼ ⟶ Spec (R' ⊗ Γ(Yⱼ))`. -/
def glα : (j : WalkingSpan) → (glF K gV π R' ψ₀ ψ₁).obj j ⟶ (span (a0 K gV π R') (a1 K gV π R')).obj j
  | none => Spec.map (CommRingCat.ofHom (algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1)) E₀₁))
  | some WalkingPair.left => Spec.map (CommRingCat.ofHom (algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0)) E₀))
  | some WalkingPair.right => Spec.map (CommRingCat.ofHom (algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 1)) E₁))

section FinEt

end FinEt

section Et

end Et

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

theorem cocExtFun_add (W : X.Etale) (p : ℕ) (a b : LinearMap.ker (secSc Λ I W p).g.hom) :
    cocExtFun Λ I W p (a + b) = cocExtFun Λ I W p a + cocExtFun Λ I W p b := by
  rw [cocExtFun, cocExtFun, cocExtFun, I.add_extMk]
  congr 1
  rw [cocSec_add, map_add]

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_StkBC =====
section

/-!
# S4-EtPBC-A, L1f: the base change map on stalks

Generic form: for `g : P ⟶ S`, a geometric point `s` of `S`, a sheaf `F` on `P`, `n : ℕ`, a presheaf `Q` on `S` and
additive bijections `e V : Q(V) ≃+ Ext^n(Λ[g⁻¹ V], F)` natural in `V` (`GermNat`), the germ maps
`germBC j = Delta.bc j ∘ e` (base change along the units `bcUnit`) are compatible, so they define `stalkBC` on the fibre
`Q_s` of `Q`. It is surjective / injective when base change is surjective / injective on germs (`BCSurj` / `BCInj`):
`stalkEquiv : Q_s ≃+ Ext^n(Λ_{P_s}, ι^* F)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

variable (F : EtSh Λ P) (n : ℕ) (Q : (S.Etale)ᵒᵖ ⥤ ModuleCat.{u} Λ)
  (e : ∀ V : S.Etale, Q.obj (op V) ≃+ Ext.{u} (freeSh Λ ((etPull g).obj V)) F n)

/-- The germ base change map at `(V, v)`. -/
def germBC (j : Nbhd s) : Q.obj (op j.1) →+ Ext.{u} (unitSh Λ (fib g s)) ((pull (fibι g s) Λ).obj F) n :=
  (Delta.bc (pull (fibι g s) Λ) (nbhdSys Λ g s) (unitSh Λ (fib g s)) (bcUnit Λ g s) j F n).comp
    (e j.1).toAddMonoidHom

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_Inj0c =====
section

/-!
# S4-EtPBC-A, G1c: base change is injective on germs in degree `0` (universally closed `g`)

* `fibB j x`: the fibre point `σ_v(x̄)` of `x̄ = geomPtAt x` over `ι⁻¹(g⁻¹ V)`; `cpt_fibB`: its point is `fibToNbhd x`;
* **`fibToNbhd_not_mem_supp`**: if `bc_j α = 0` then no point of `P_s` lands in the support of `sec0 α`;
* `fibCmp`, **`exists_fibToNbhd`**: every point of `g⁻¹ V` over `v` comes from `P_s`;
* **`bcInj_zero`**: for universally closed `g`, `BCInj Λ g s 0 G` for every sheaf `G` (the support of `sec0 α` is closed,
  its image in `V` is closed and misses `v`; shrink `V` to the complement, where every germ vanishes).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech

universe u

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- **No point of the fibre lies in the support** of a section killed by base change. -/
theorem fibToNbhd_not_mem_supp (j : Nbhd s) (G : EtSh Λ P) (α : Ext.{u} ((nbhdSys Λ g s).obj j) G 0)
    (h : Delta.bc (pull (fibι g s) Λ) (nbhdSys Λ g s) (unitSh Λ (fib g s)) (bcUnit Λ g s) j G 0 α = 0)
    (x : fib g s) : fibToNbhd g s j x ∉ supp G (sec0 Λ g s j G α) := by
  rw [← cpt_fibB g s j x]
  refine cpt_not_mem_supp (fibι g s) (geomPtAt x) G (V := (etPull g).obj j.1) (fibB g s j x)
    (sec0 Λ g s j G α) ?_
  refine comap_germ_eq_zero (fibι g s) (geomPtAt x) G (V := (etPull g).obj j.1) (fibB g s j x)
    (sec0 Λ g s j G α) ?_
  have hq := sec_of_bc_zero Λ g s j G α h
  have hw := ConcreteCategory.congr_hom ((geomPtAt x).point.toPresheafFiber_w (nbhdSec g s j) (geomPtAt x).top
    ((pull (fibι g s) Λ).obj G).obj)
    ((((pullAdj (fibι g s) Λ).unit.app G).hom.app (op ((etPull g).obj j.1))).hom (sec0 Λ g s j G α))
  calc _ = ((geomPtAt x).point.toPresheafFiber (etId (fib g s)) (geomPtAt x).top ((pull (fibι g s) Λ).obj G).obj).hom
        ((((pull (fibι g s) Λ).obj G).obj.map (nbhdSec g s j).op).hom
          ((((pullAdj (fibι g s) Λ).unit.app G).hom.app (op ((etPull g).obj j.1))).hom (sec0 Λ g s j G α))) :=
        hw.symm
    _ = 0 := by rw [hq, map_zero]

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_Inj0dg =====
section

/-!
# S4-EtPBC-A, G1d part 1b: the point `v` lies in `good`, and the lifted point `goodPt`
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech

universe u

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

theorem v_mem_good [UniversallyClosed g] (j : Nbhd s) (G : EtSh Λ P) (α : Ext.{u} ((nbhdSys Λ g s).obj j) G 0)
    (h : Delta.bc (pull (fibι g s) Λ) (nbhdSys Λ g s) (unitSh Λ (fib g s)) (bcUnit Λ g s) j G 0 α = 0)
    (w : Spec (CommRingCat.of s.Ω)) : j.2.left w ∈ good Λ g s j G α := by
  show j.2.left w ∉ bad Λ g s j G α
  rintro ⟨t, ht, hte⟩
  have hw : w = default := Subsingleton.elim _ _
  subst hw
  obtain ⟨x, rfl⟩ := exists_fibToNbhd g s j t hte
  exact fibToNbhd_not_mem_supp Λ g s j G α h x ht

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

end Phi

section Main

variable {Λ : Type u} [CommRing Λ] {Y P : Scheme.{u}} (π : Y ⟶ P) [IsFinite π] (t : GeomPt P)
  {M : ModuleCat.{u} Λ}

/-- **Sections of `M_Y` with prescribed values along a finite fibre** (after refining the neighbourhood). -/
theorem exists_sec_vals (j : Nbhd t) (v : ↑(pullback j.1.hom π) → M) :
    ∃ (j' : Nbhd t) (_ : j' ⟶ j) (z : (constSh Λ Y M).obj.obj (op ((etPull π).obj j'.1))),
      ∀ x : fib π t, cval z (fibToNbhd π t j' x) = v (fibToNbhd π t j x) := by
  obtain ⟨j₁, a₁, hA⟩ := exists_affine_le t j
  haveI := hA
  obtain ⟨j', a', z, hz⟩ := exists_sec_vals_aff (Λ := Λ) π t j₁ (fun w => v (((etPull π).map a₁.1).left w))
  refine ⟨j', a' ≫ a₁, z, fun x => (hz x).trans (congrArg v ?_)⟩
  exact congrArg (fun φ => φ.base x) (fibToNbhd_map π t a₁)

end Main

end RamanujanPetersson.EtPBC.FBC

end

end

-- ===== S4.Def_RP_EtPBC_A_DescG5 =====
section

/-!
# S4-EtPBC-A, R4-T1d (part 2): the sheets cover `U₀`, the descended section `σ`

* `sheet_cover`: the sheets `sheetE ν : V ⟶ U0E` cover `U0E` (every prime of `B(U)` comes from a sheet).
* `cU_kL`, `cval_dif_sheet`, `dif_sheet`: if `gi ≫ sheetE i = gj ≫ sheetE j` then `dif gi gj = j - i`
  (pointwise: the pair `(gi, gj)` lands in `Spec (C ⊗ C)` over an affine `U`, and `key_sheet`).
* `exists_sigma`: the sections `e + a(ν)` on the sheets glue to `σ ∈ E(U₀)`; `b_sigma`: `b σ` is the pull-back of `q`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.DescG

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.DescA TensorProduct

universe u

section Gen

end Gen

section Pt

end Pt

section Cover

variable {X : Scheme.{u}} (V : X.Etale) [IsAffineHom V.hom] [Surjective V.hom] {Λ : Type u} [CommRing Λ]
  {M : ModuleCat.{u} Λ} [Fintype M] [DecidableEq M] {E Q : EtSh Λ X} (a : constSh Λ X M ⟶ E) (b : E ⟶ Q)
  (hab : a ≫ b = 0) (hS : (ShortComplex.mk a b hab).ShortExact) (e : E.obj.obj (op V))
  (he : ∀ (W : X.Etale) (w₁ w₂ : W ⟶ V), (b.hom.app (op W)).hom ((E.obj.map w₁.op).hom e) =
    (b.hom.app (op W)).hom ((E.obj.map w₂.op).hom e))

/-- **`b σ` is the pull-back of `q`** (when `b e` is). -/
theorem b_sigma (s : E.obj.obj (op (U0E V a b hab hS e he)))
    (hs : ∀ ν : M, (E.obj.map (sheetE V a b hab hS e he ν).op).hom s =
      e + (a.hom.app (op V)).hom ((constUnit M V).hom ν))
    (q : Q.obj.obj (op (etId X)))
    (hq : (b.hom.app (op V)).hom e = (Q.obj.map ((PtSec.etId_isTerminal X).from V).op).hom q) :
    (b.hom.app (op (U0E V a b hab hS e he))).hom s =
      (Q.obj.map ((PtSec.etId_isTerminal X).from (U0E V a b hab hS e he)).op).hom q := by
  refine sep_of_cover Q (sheetE V a b hab hS e he) (sheet_cover V a b hab hS e he) _ _ fun ν => ?_
  have hn := congrArg (fun φ => φ.hom s) (b.hom.naturality (sheetE V a b hab hS e he ν).op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hn
  rw [← hn, hs, map_add, sec_fg (S := ShortComplex.mk a b hab) V, add_zero, hq, ← LinearMap.comp_apply,
    ← ModuleCat.hom_comp, ← Q.obj.map_comp, ← op_comp,
    (PtSec.etId_isTerminal X).hom_ext (sheetE V a b hab hS e he ν ≫ _) ((PtSec.etId_isTerminal X).from V)]

end Cover

end RamanujanPetersson.EtPBC.DescG

end

end


