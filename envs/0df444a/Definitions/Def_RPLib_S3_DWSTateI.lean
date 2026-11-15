-- Prove2me | Definitions.Def_RPLib_S3_DWSTateI
-- name    : RPLib_S3_DWSTateI
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:35:59.612828+00:00
-- url     : https://prove2.me/theorems/39459881-d137-45de-bb76-fac7e6b8ef86
-- title:
--   Weight-two Ramanujan-Petersson library: prime-to-`p` isogenies are Vélu quotients (b7a) and are `R`-linear (b7b)
-- statement:
--   Prime-to-`p` isogenies are Vélu quotients (b7a) and are `R`-linear (b7b).
--
--   * `exists_isQuot_ker`: if `u : E → E₁`, `w : E₁ → E` are `F_q`-isogenies with `w u = [N]`, `u w = [N]`, `p ∤ N`,
--     then `u` itself is a Vélu quotient by its kernel (`IsQuot u.ker u ψ n` for some dual `ψ`).
--   * `commSub s s₁ u`: the subring of `R` whose actions are intertwined by `u`; `mem_commSub_of_natCast_mul`
--     (cancel a factor prime to `p`); **`mem_commSub_of_frob`**: a Frobenius-equivariant `u` between curves with
--     Frobenius-normalised `R`-structures (`ι π = π_E`, `ι₁ π = π_{E₁}`, `p ∤ im π`) is `R`-linear.
--   * `IsQuot.surjψ`, `IsQuot.map_tors` (`ψ(E₁[n]) = G`), `IsQuot.mem_of_ι` (`G` is `R`-stable).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSTateH

/-!
# S3-DWS-Tate, part I: prime-to-`p` isogenies are Vélu quotients (b7a) and are `R`-linear (b7b)

* `exists_isQuot_ker`: if `u : E → E₁`, `w : E₁ → E` are `F_q`-isogenies with `w u = [N]`, `u w = [N]`, `p ∤ N`,
  then `u` itself is a Vélu quotient by its kernel (`IsQuot u.ker u ψ n` for some dual `ψ`).
* `commSub s s₁ u`: the subring of `R` whose actions are intertwined by `u`; `mem_commSub_of_natCast_mul`
  (cancel a factor prime to `p`); **`mem_commSub_of_frob`**: a Frobenius-equivariant `u` between curves with
  Frobenius-normalised `R`-structures (`ι π = π_E`, `ι₁ π = π_{E₁}`, `p ∤ im π`) is `R`-linear.
* `IsQuot.surjψ`, `IsQuot.map_tors` (`ψ(E₁[n]) = G`), `IsQuot.mem_of_ι` (`G` is `R`-stable).
-/

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

section B7

variable {F : Type*} [Field F] [Fintype F] {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

variable {W W₁ : WeierstrassCurve F} [W.IsElliptic] [W₁.IsElliptic]

lemma natCast_ne_zero_L' {N : ℕ} (hNF : (N : F) ≠ 0) : (N : L) ≠ 0 := by
  rw [← map_natCast (algebraMap F L)]
  exact (_root_.map_ne_zero (algebraMap F L)).mpr hNF

/-- The kernel of `u` lies in `E[N]` when `w u = [N]`. -/
lemma ker_le_torsN {N : ℕ} {u : Pt W L →+ Pt W₁ L} {w : Pt W₁ L →+ Pt W L}
    (hwu : ∀ P, w (u P) = N • P) : u.ker ≤ torsN W L N := fun P hP => by
  rw [mem_torsN, ← hwu, (AddMonoidHom.mem_ker).mp hP, map_zero]

/-- **(b7a) A prime-to-`p` isogeny is a Vélu quotient by its kernel.** -/
theorem exists_isQuot_ker {N : ℕ} (hNF : (N : F) ≠ 0) {u : Pt W L →+ Pt W₁ L} {w : Pt W₁ L →+ Pt W L}
    (hu : IsIsog u) (hw : IsIsog w) (hwu : ∀ P, w (u P) = N • P) (huw : ∀ Q, u (w Q) = N • Q)
    (hfu : ∀ P, u (RPLib.EllFq.frob W L P) = RPLib.EllFq.frob W₁ L (u P)) :
    ∃ ψ : Pt W₁ L →+ Pt W L, ∃ n : ℕ, IsQuot u.ker u ψ n := by
  have hle := ker_le_torsN (L := L) hwu
  haveI := finite_torsN (W := W) (L := L) hNF
  haveI : Finite u.ker := Finite.of_injective _ (AddSubgroup.inclusion_injective hle)
  have hG : (Nat.card u.ker : L) ≠ 0 := by
    obtain ⟨k, hk⟩ := AddSubgroup.card_dvd_of_le hle
    have h : (Nat.card (torsN W L N) : L) ≠ 0 := card_kerSet_ne_zero (Set.mem_singleton _) hNF
    rw [hk, Nat.cast_mul] at h
    exact left_ne_zero_of_mul h
  have hFr : ∀ T ∈ u.ker, RPLib.EllFq.frob W L T ∈ u.ker := fun T hT => by
    rw [AddMonoidHom.mem_ker] at hT ⊢
    rw [hfu, hT, map_zero]
  obtain ⟨W', hE, φ, ψ, hq⟩ := exists_isQuot u.ker hG hFr
  obtain ⟨β, hβ, hβφ, hβf⟩ := hq.factor hu (fun T hT => (AddMonoidHom.mem_ker).mp hT)
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_zero]
    intro Q hQ
    obtain ⟨P, rfl⟩ := hq.surj Q
    rw [hβφ] at hQ
    exact (hq.ker P).mpr ((AddMonoidHom.mem_ker).mpr hQ)
  obtain ⟨v, hv, hvβ, hβv, -⟩ := exists_inv_isog hNF hβinj (hq.isog.comp hw)
    (fun Q => by show β (φ (w Q)) = N • Q; rw [hβφ, huw])
  have hcomp : β.comp φ = u := AddMonoidHom.ext hβφ
  refine ⟨ψ.comp v, Nat.card u.ker, ?_⟩
  have h := hq.comp_iso hβ hv hvβ hβv (hβf hfu)
  rwa [hcomp] at h

variable {G : AddSubgroup (Pt W L)} {φ : Pt W L →+ Pt W₁ L} {ψ : Pt W₁ L →+ Pt W L} {n : ℕ}

/-- The dual of a quotient is surjective. -/
lemma IsQuot.surjψ (hq : IsQuot G φ ψ n) : Function.Surjective ψ := fun P => by
  obtain ⟨Q, hQ⟩ := nsmul_surjective (W := W) (L := L) (natCast_ne_zero_L' hq.hn) P
  exact ⟨φ Q, by rw [hq.dual1]; exact hQ⟩

/-- `ψ(E₁[n]) = G`. -/
lemma IsQuot.mem_iff_exists_tors (hq : IsQuot G φ ψ n) (P : Pt W L) :
    P ∈ G ↔ ∃ Q, n • Q = 0 ∧ ψ Q = P := by
  constructor
  · intro hP
    obtain ⟨Q, rfl⟩ := hq.surjψ P
    refine ⟨Q, ?_, rfl⟩
    rw [← hq.dual2, (hq.ker _).mpr hP]
  · rintro ⟨Q, hQ, rfl⟩
    rw [← hq.ker, hq.dual2, hQ]

/-- `G ⊆ E[n]`. -/
lemma IsQuot.nsmul_eq_zero (hq : IsQuot G φ ψ n) {P : Pt W L} (hP : P ∈ G) : n • P = 0 := by
  rw [← hq.dual1, (hq.ker P).mpr hP, map_zero]

end B7

section Comm

variable {F : Type*} [Field F] [Fintype F] {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

variable {W W₁ : WeierstrassCurve F} [W.IsElliptic] [W₁.IsElliptic] {R : Type*} [CommRing R]

lemma OAct.ι_mul_apply (s : OAct R W L) (x y : R) (P : Pt W L) : s.ι (x * y) P = s.ι x (s.ι y P) := by
  rw [map_mul]; rfl

lemma OAct.ι_add_apply (s : OAct R W L) (x y : R) (P : Pt W L) : s.ι (x + y) P = s.ι x P + s.ι y P := by
  rw [map_add]; rfl

lemma OAct.ι_neg_apply (s : OAct R W L) (x : R) (P : Pt W L) : s.ι (-x) P = -s.ι x P := by
  rw [map_neg]; rfl

lemma OAct.ι_one_apply (s : OAct R W L) (P : Pt W L) : s.ι 1 P = P := by
  rw [map_one]; rfl

lemma OAct.ι_zero_apply (s : OAct R W L) (P : Pt W L) : s.ι 0 P = 0 := by
  rw [map_zero]; rfl

/-- The elements of `R` whose actions on `E` and `E₁` are intertwined by `u`. -/
def commSub (s : OAct R W L) (s₁ : OAct R W₁ L) (u : Pt W L →+ Pt W₁ L) : Subring R where
  carrier := {r | ∀ P, u (s.ι r P) = s₁.ι r (u P)}
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    intro P
    rw [s.ι_mul_apply, s₁.ι_mul_apply, hx, hy]
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    intro P
    rw [s.ι_one_apply, s₁.ι_one_apply]
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    intro P
    rw [s.ι_add_apply, s₁.ι_add_apply, map_add, hx, hy]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    intro P
    rw [s.ι_zero_apply, s₁.ι_zero_apply, map_zero]
  neg_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    intro P
    rw [s.ι_neg_apply, s₁.ι_neg_apply, map_neg, hx]

variable {s : OAct R W L} {s₁ : OAct R W₁ L} {u : Pt W L →+ Pt W₁ L}

lemma mem_commSub {r : R} : r ∈ commSub s s₁ u ↔ ∀ P, u (s.ι r P) = s₁.ι r (u P) := Iff.rfl

/-- Cancel a factor `n` prime to `p` (`[n]` is onto `E(L)`). -/
lemma mem_commSub_of_natCast_mul {n : ℕ} (hn : (n : F) ≠ 0) {r : R} (h : (n : R) * r ∈ commSub s s₁ u) :
    r ∈ commSub s s₁ u := by
  rw [mem_commSub] at h ⊢
  intro P
  obtain ⟨Q, hQ⟩ := nsmul_surjective (W := W) (L := L) (natCast_ne_zero_L' hn) P
  have hQ' : n • Q = P := hQ
  rw [← hQ']
  have h1 := h Q
  rw [s.ι_mul_apply, s₁.ι_mul_apply, s.natCast_apply, s₁.natCast_apply] at h1
  rw [map_nsmul (s.ι r), h1, map_nsmul u, map_nsmul (s₁.ι r)]

lemma mem_commSub_of_intCast_mul {z : ℤ} (hz : (z.natAbs : F) ≠ 0) {r : R} (h : (z : R) * r ∈ commSub s s₁ u) :
    r ∈ commSub s s₁ u := by
  apply mem_commSub_of_natCast_mul hz
  obtain ⟨m, rfl | rfl⟩ : ∃ m : ℕ, z = m ∨ z = -m := ⟨z.natAbs, Int.natAbs_eq z⟩
  · simpa using h
  · simpa using h

/-- **(b7b) Frobenius-equivariant maps are `R`-linear** for Frobenius-normalised `R`-structures. -/
theorem mem_commSub_of_frob {a b : ℤ} {s : OAct (QuadraticAlgebra ℤ a b) W L}
    {s₁ : OAct (QuadraticAlgebra ℤ a b) W₁ L} {π : QuadraticAlgebra ℤ a b} (hπ : s.ι π = piE W L)
    (hπ₁ : s₁.ι π = piE W₁ L) (hπF : (π.im.natAbs : F) ≠ 0) {u : Pt W L →+ Pt W₁ L}
    (hfu : ∀ P, u (RPLib.EllFq.frob W L P) = RPLib.EllFq.frob W₁ L (u P)) (r : QuadraticAlgebra ℤ a b) :
    r ∈ commSub s s₁ u := by
  have hπmem : π ∈ commSub s s₁ u := mem_commSub.mpr fun P => by
    rw [hπ, hπ₁]; exact hfu P
  apply mem_commSub_of_intCast_mul hπF
  have e : ((π.im : ℤ) : QuadraticAlgebra ℤ a b) * r =
      ((π.im * r.re - r.im * π.re : ℤ) : QuadraticAlgebra ℤ a b) +
        ((r.im : ℤ) : QuadraticAlgebra ℤ a b) * π := by
    ext <;> simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_add,
      QuadraticAlgebra.im_add, QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast, Int.cast_id] <;> ring
  rw [e]
  exact add_mem (intCast_mem _ _) (mul_mem (intCast_mem _ _) hπmem)

/-- An `R`-linear map sends `R`-stable data along: `G = ker u` is `R`-stable. -/
lemma ι_mem_ker (h : ∀ r : R, r ∈ commSub s s₁ u) (r : R) {P : Pt W L} (hP : P ∈ u.ker) :
    s.ι r P ∈ u.ker := by
  rw [AddMonoidHom.mem_ker] at hP ⊢
  rw [(mem_commSub.mp (h r)) P, hP, map_zero]

/-- If `u` is `R`-linear and `w u = [N]`, `u w = [N]` with `p ∤ N`, then `w` is `R`-linear. -/
lemma commSub_of_inverse {N : ℕ} (hNF : (N : F) ≠ 0) {w : Pt W₁ L →+ Pt W L}
    (huw : ∀ Q, u (w Q) = N • Q) (hwu : ∀ P, w (u P) = N • P) (h : ∀ r : R, r ∈ commSub s s₁ u) (r : R) :
    r ∈ commSub s₁ s w := by
  rw [mem_commSub]
  intro Q
  obtain ⟨Q', hQ'⟩ := nsmul_surjective (W := W₁) (L := L) (natCast_ne_zero_L' hNF) Q
  have e : u (w Q') = Q := by rw [huw]; exact hQ'
  rw [← e, ← (mem_commSub.mp (h r)) (w Q'), hwu, hwu, map_nsmul]

end Comm

end RPLib.DWS


