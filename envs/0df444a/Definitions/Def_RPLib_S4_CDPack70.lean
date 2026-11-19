-- Prove2me | Definitions.Def_RPLib_S4_CDPack70
-- name    : RPLib_S4_CDPack70
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T06:21:08.360646+00:00
-- url     : https://prove2.me/theorems/a22e3bb7-4a0a-4127-9b84-07fffb232b13
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 70 of 71
-- statement:
--   Part 70 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacAlg_Norm`: Core B algebra, part 2: `P_π` is monic of degree `2g` and `deg F = ∏ F(a)` (Milne 10.22, L5/L6)
--   * `Def_RP_JacAlg_Zeta`: Core B algebra, part 4: the zeta link (A5) and the roots of `P_π` (A6 applied)
--   * `Def_RP_JacAlg_Div`: Core B algebra, part 5: divisibility (unit S4-JacAlg, lemma L2 = route A1)
--   * `Def_RP_JacAlg_Charpoly`: Core B algebra, part 8: `P_π = charpoly(T_l π)` (unit S4-JacAlg, L4/L5 = Milne 10.20-10.22, steps C1, C2)
--   * `Def_RP_JacAlg`: Core B algebra (unit S4-JacAlg, route S4_COREB_ROUTE.md section 3, lemmas L1-L7)
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack37
import Definitions.Def_RPLib_S4_CDPack49
import Definitions.Def_RPLib_S4_CDPack12

/-!
# Curve-duality library package, part 70 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacAlg_Norm`: Core B algebra, part 2: `P_π` is monic of degree `2g` and `deg F = ∏ F(a)` (Milne 10.22, L5/L6)
* `Def_RP_JacAlg_Zeta`: Core B algebra, part 4: the zeta link (A5) and the roots of `P_π` (A6 applied)
* `Def_RP_JacAlg_Div`: Core B algebra, part 5: divisibility (unit S4-JacAlg, lemma L2 = route A1)
* `Def_RP_JacAlg_Charpoly`: Core B algebra, part 8: `P_π = charpoly(T_l π)` (unit S4-JacAlg, L4/L5 = Milne 10.20-10.22, steps C1, C2)
* `Def_RP_JacAlg`: Core B algebra (unit S4-JacAlg, route S4_COREB_ROUTE.md section 3, lemmas L1-L7)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacAlg_Norm =====
section

/-!
# Core B algebra, part 2: `P_π` is monic of degree `2g` and `deg F = ∏ F(a)` (Milne 10.22, L5/L6)

For `D : DegreeData π g p`, `P_π = D.charPoly` (`P_π(n) = deg(n - π)`).
* `charPoly_monic`, `charPoly_natDegree`: `P_π` is monic of degree `2g`. Proof: for `a = 2^(2g)` the pencil
  `b ↦ deg(a - bX)` is a polynomial of degree `≤ 2g` which equals `Σ_k p_k a^k b^(2g-k)` at the `2g+1`
  divisors `b = 2^j` of `a`; at `b = 0` it gives `a^(2g) = p_(2g) a^(2g)`.
* `deg_eq_prod_roots`: over any algebraically closed field `K` of characteristic `0`,
  `deg F = ∏_{a ∈ roots P_π} F(a)` for every `F ∈ ℤ[X]` (Milne Lemma 10.22, without multivariable
  polynomial functions: induction on `deg F` with the pencil `s ↦ deg(F - F(s))`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacAlg

open Polynomial Finset

namespace DegreeData

variable {A : Type*} [AddCommGroup A] {π : Module.End ℤ A} {g p : ℕ} (D : DegreeData π g p)

theorem natAbs_pow_cast {K : Type*} [CommRing K] (b : ℤ) :
    (((b.natAbs ^ (2 * g) : ℕ)) : K) = (b : K) ^ (2 * g) := by
  rw [Nat.cast_pow, pow_mul, pow_mul]
  congr 1
  rw [← Int.cast_natCast (R := K), ← Int.cast_pow, Int.natAbs_sq b, Int.cast_pow]

/-- `deg(b n - b X) = b^(2g) P_π(n)`. -/
theorem deg_mul_sub (b n : ℤ) :
    (D.deg (((b * n : ℤ) : ℤ[X]) - (b : ℤ[X]) * X) : ℚ) = (b : ℚ) ^ (2 * g) * D.charPoly.eval (n : ℚ) := by
  have : (((b * n : ℤ) : ℤ[X]) - (b : ℤ[X]) * X) = (b : ℤ[X]) * ((n : ℤ[X]) - X) := by push_cast; ring
  rw [this, D.deg_mul, D.deg_intCast, charPoly_eval, Nat.cast_mul, natAbs_pow_cast]

/-- The comparison polynomial `V(b) = Σ_k p_k a^k b^(2g-k)` (`= b^(2g) P(a/b)` for `b ≠ 0`). -/
noncomputable def homPoly (a : ℚ) : ℚ[X] :=
  ∑ k ∈ range (2 * g + 1), C (D.charPoly.coeff k * a ^ k) * X ^ (2 * g - k)

theorem homPoly_eval (a b : ℚ) :
    (D.homPoly a).eval b = ∑ k ∈ range (2 * g + 1), D.charPoly.coeff k * a ^ k * b ^ (2 * g - k) := by
  simp [homPoly, eval_finsetSum]

theorem homPoly_natDegree_le (a : ℚ) : (D.homPoly a).natDegree ≤ 2 * g := by
  unfold homPoly
  refine natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le _ _)

theorem homPoly_eval_zero (a : ℚ) : (D.homPoly a).eval 0 = D.charPoly.coeff (2 * g) * a ^ (2 * g) := by
  rw [homPoly_eval, Finset.sum_eq_single (2 * g)]
  · simp
  · intro k hk hne
    have : 2 * g - k ≠ 0 := by
      have := Finset.mem_range.mp hk; omega
    simp [zero_pow this]
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) h

theorem homPoly_eval_mul (b n : ℚ) :
    (D.homPoly (b * n)).eval b = b ^ (2 * g) * D.charPoly.eval n := by
  rw [homPoly_eval, eval_eq_sum_range' (n := 2 * g + 1) (Nat.lt_succ_of_le D.charPoly_natDegree_le),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ 2 * g := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have : b ^ (2 * g) = b ^ k * b ^ (2 * g - k) := by rw [← pow_add, Nat.add_sub_cancel' hk']
  rw [this, mul_pow]; ring

theorem charPoly_coeff_top : D.charPoly.coeff (2 * g) = 1 := by
  set a : ℤ := 2 ^ (2 * g) with ha
  set T : ℚ[X] := D.polyOf (-X) (a : ℤ[X]) with hT
  have hTeval : ∀ b : ℤ, T.eval (b : ℚ) = (D.deg ((a : ℤ[X]) - (b : ℤ[X]) * X) : ℚ) := by
    intro b
    rw [hT, polyOf_eval]
    congr 2
    rw [zsmul_eq_mul]; ring
  have hTV : T = D.homPoly (a : ℚ) := by
    apply eq_of_degree_sub_lt_of_eval_finset_eq ((range (2 * g + 1)).image fun j => ((2 : ℚ) ^ j))
    · rw [Finset.card_image_of_injective _ (pow_right_injective₀ (by norm_num) (by norm_num))]
      rw [card_range]
      refine (degree_sub_le _ _).trans_lt ?_
      refine max_lt ?_ ?_
      · exact (degree_le_natDegree.trans (WithBot.coe_le_coe.mpr (D.polyOf_natDegree_le _ _))).trans_lt
          (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self _))
      · exact (degree_le_natDegree.trans (WithBot.coe_le_coe.mpr (D.homPoly_natDegree_le _))).trans_lt
          (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self _))
    · intro x hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      have hj' : j ≤ 2 * g := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hab : a = 2 ^ j * 2 ^ (2 * g - j) := by rw [ha, ← pow_add, Nat.add_sub_cancel' hj']
      have h1 := hTeval (2 ^ j)
      have h2 := D.deg_mul_sub (2 ^ j) (2 ^ (2 * g - j))
      rw [← hab] at h2
      push_cast at h1 h2
      rw [h1, h2, show ((a : ℤ) : ℚ) = (2 : ℚ) ^ j * 2 ^ (2 * g - j) by rw [hab]; push_cast; ring,
        homPoly_eval_mul]
  have h0 := congrArg (fun P : ℚ[X] => P.eval 0) hTV
  rw [homPoly_eval_zero, show (0 : ℚ) = ((0 : ℤ) : ℚ) by simp, hTeval] at h0
  simp only [Int.cast_zero, zero_mul, sub_zero] at h0
  rw [D.deg_intCast, natAbs_pow_cast] at h0
  have hane : ((a : ℤ) : ℚ) ^ (2 * g) ≠ 0 := pow_ne_zero _ (by rw [ha]; positivity)
  have := mul_right_cancel₀ hane (h0.symm.trans (one_mul _).symm)
  exact this

theorem charPoly_natDegree : D.charPoly.natDegree = 2 * g :=
  le_antisymm D.charPoly_natDegree_le
    (le_natDegree_of_ne_zero (by rw [D.charPoly_coeff_top]; exact one_ne_zero))

theorem charPoly_monic : D.charPoly.Monic := by
  rw [Monic, leadingCoeff, D.charPoly_natDegree, D.charPoly_coeff_top]


section Roots

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

omit [IsAlgClosed K] in
theorem eval_map_algebraMap_intCast (Q : ℚ[X]) (s : ℤ) :
    (Q.map (algebraMap ℚ K)).eval (s : K) = algebraMap ℚ K (Q.eval (s : ℚ)) := by
  rw [← map_intCast (algebraMap ℚ K) s, eval_map, eval₂_at_apply]

omit [CharZero K] [IsAlgClosed K] in
theorem eval_map_intCast (F : ℤ[X]) (s : ℤ) :
    (F.map (Int.castRingHom K)).eval (s : K) = ((F.eval s : ℤ) : K) := by
  rw [show (s : K) = Int.castRingHom K s by simp, eval_map, eval₂_at_apply]; simp

theorem charPoly_map_eval (x : K) :
    (D.charPoly.map (algebraMap ℚ K)).eval x =
      ((D.charPoly.map (algebraMap ℚ K)).roots.map fun a => x - a).prod := by
  have hm : (D.charPoly.map (algebraMap ℚ K)).Monic := D.charPoly_monic.map _
  have hc : Multiset.card (D.charPoly.map (algebraMap ℚ K)).roots =
      (D.charPoly.map (algebraMap ℚ K)).natDegree := IsAlgClosed.card_roots_eq_natDegree
  conv_lhs => rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hc]
  rw [eval_multiset_prod, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro a _
  simp

theorem card_roots_charPoly : Multiset.card (D.charPoly.map (algebraMap ℚ K)).roots = 2 * g := by
  rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_map, D.charPoly_natDegree]

/-- Milne Lemma 10.22 for `ℤ[π]`: `deg F = ∏_{a ∈ roots P_π} F(a)` in any algebraically closed `K ⊇ ℚ`. -/
theorem deg_eq_prod_roots (F : ℤ[X]) :
    (D.deg F : K) = ((D.charPoly.map (algebraMap ℚ K)).roots.map
      fun a => (F.map (Int.castRingHom K)).eval a).prod := by
  induction hd : F.natDegree using Nat.strong_induction_on generalizing F with
  | _ d IH =>
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · rw [h0] at hd
    rw [eq_C_of_natDegree_eq_zero hd]
    have h := D.deg_C_mul (F.coeff 0) 1
    rw [mul_one, D.deg_one, mul_one] at h
    rw [h, natAbs_pow_cast]
    simp only [Polynomial.map_C, eval_C, Multiset.map_const', Multiset.prod_replicate,
      D.card_roots_charPoly, Int.coe_castRingHom]
  · have hinj : Function.Injective (Int.castRingHom K) := Int.cast_injective
    set FK := F.map (Int.castRingHom K) with hFK
    set PK := D.charPoly.map (algebraMap ℚ K) with hPK
    set R := D.polyOf 1 F with hR
    have key : ∀ s : ℤ, (R.map (algebraMap ℚ K)).eval (((-(F.eval s) : ℤ)) : K) =
        (PK.roots.map fun a => FK.eval (s : K) - FK.eval a).prod := by
      intro s
      set G := (F - C (F.eval s)) /ₘ (X - C s) with hGdef
      have hG : (X - C s) * G = F - C (F.eval s) :=
        mul_divByMonic_eq_iff_isRoot.mpr (by simp [IsRoot])
      have hGdeg : G.natDegree < d := by
        rw [hGdef, natDegree_divByMonic _ (monic_X_sub_C _), natDegree_sub_C, natDegree_X_sub_C, hd]
        omega
      have IHG := IH _ hGdeg G rfl
      have h1 : (D.deg (F - C (F.eval s)) : ℚ) = R.eval ((-(F.eval s) : ℤ) : ℚ) := by
        rw [hR, polyOf_eval, zsmul_one, Int.cast_neg, sub_eq_add_neg, add_comm, eq_intCast C]
      have hneg : -(X - C s) = ((s : ℤ[X]) - X) := by rw [eq_intCast C]; ring
      have h2 : D.deg (F - C (F.eval s)) = D.deg ((s : ℤ[X]) - X) * D.deg G := by
        rw [← hG, D.deg_mul, ← hneg, D.deg_neg]
      have h3 : (D.deg ((s : ℤ[X]) - X) : K) = PK.eval (s : K) := by
        rw [hPK, eval_map_algebraMap_intCast, charPoly_eval, map_natCast]
      have hGa : ∀ a : K, (s - a) * (G.map (Int.castRingHom K)).eval a = FK.eval (s : K) - FK.eval a := by
        intro a
        have := congrArg (fun P : ℤ[X] => (P.map (Int.castRingHom K)).eval a) hG
        simp only [Polynomial.map_mul, Polynomial.map_sub, map_X, map_C, eval_mul, eval_sub, eval_X,
          eval_C] at this
        rw [hFK, eval_map_intCast]
        simp only [eq_intCast] at this ⊢
        linear_combination -this
      rw [eval_map_algebraMap_intCast, ← h1, map_natCast, h2, Nat.cast_mul, h3, IHG, charPoly_map_eval,
        ← Multiset.prod_map_mul]
      congr 1
      exact Multiset.map_congr rfl fun a _ => hGa a
    have hpoly : (R.map (algebraMap ℚ K)).comp (-FK) =
        (PK.roots.map fun a => FK - C (FK.eval a)).prod := by
      apply eq_of_infinite_eval_eq
      apply Set.Infinite.mono _ (Set.infinite_range_of_injective (Int.cast_injective (α := K)))
      rintro _ ⟨s, rfl⟩
      simp only [Set.mem_setOf_eq, eval_comp, eval_neg, eval_multiset_prod, Multiset.map_map,
        Function.comp_def, eval_sub, eval_C]
      rw [hFK, eval_map_intCast, ← Int.cast_neg, key s, eval_map_intCast]
    obtain ⟨c, hc⟩ := IsAlgClosed.exists_root FK (by
      rw [hFK, degree_map_eq_of_injective hinj, degree_eq_natDegree (by rintro rfl; simp at hd; omega), hd]
      exact_mod_cast hpos.ne')
    have hc' := congrArg (eval c) hpoly
    simp only [eval_comp, eval_neg, hc.eq_zero, neg_zero, eval_multiset_prod, Multiset.map_map,
      Function.comp_def, eval_sub, eval_C, zero_sub] at hc'
    rw [show (PK.roots.map fun x => -eval x FK) = (PK.roots.map fun x => eval x FK).map Neg.neg by
      rw [Multiset.map_map]; rfl, Multiset.prod_map_neg, Multiset.card_map, D.card_roots_charPoly, pow_mul,
      neg_one_sq, one_pow, one_mul] at hc'
    rw [← hc', show (0 : K) = ((0 : ℤ) : K) by simp, eval_map_algebraMap_intCast, hR, polyOf_eval,
      zero_smul, zero_add, map_natCast]

end Roots

end DegreeData

end RamanujanPetersson.JacAlg

end

-- ===== S4.Def_RP_JacAlg_Zeta =====
section

/-!
# Core B algebra, part 4: the zeta link (A5) and the roots of `P_π` (A6 applied)

* `deg_one_sub_X_pow`: `deg(1 - π^m) = ∏_j (1 - a_j^m)` over the roots `a_j` of `P_π` (A5).
* `card_ker_one_sub_X_pow`: `#Ker(1 - π^m) = deg(1 - π^m)` (D3, `p ∤ 1`).
* `roots_charPoly_eq`, `charPoly_map_eq_prod`: with `h_m = ∏_i (1 - ω_i^m)` and RH `|ω_i| = √q`, the complex
  roots of `P_π` are the `ω_i` and `P_π = ∏_i (X - ω_i)` (A6 via `multiset_eq_of_prod_one_sub_pow_sqrt`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacAlg

open Polynomial

namespace DegreeData

variable {A : Type*} [AddCommGroup A] {π : Module.End ℤ A} {g p : ℕ} (D : DegreeData π g p)

section Roots

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- A5: `deg(1 - π^m) = ∏_j (1 - a_j^m)` over the roots `a_j` of `P_π` in `K`. -/
theorem deg_one_sub_X_pow (m : ℕ) :
    (D.deg (1 - X ^ m) : K) =
      ((D.charPoly.map (algebraMap ℚ K)).roots.map fun a => 1 - a ^ m).prod := by
  rw [D.deg_eq_prod_roots]
  congr 1
  apply Multiset.map_congr rfl
  intro a _
  simp

/-- `deg π = ∏_j a_j`. -/
theorem deg_X_eq_prod_roots :
    (D.deg X : K) = (D.charPoly.map (algebraMap ℚ K)).roots.prod := by
  rw [D.deg_eq_prod_roots]
  congr 1
  conv_rhs => rw [← Multiset.map_id (D.charPoly.map (algebraMap ℚ K)).roots]
  apply Multiset.map_congr rfl
  intro a _
  simp

/-- If `π` is injective, `0` is not a root of `P_π`. -/
theorem zero_not_mem_roots (hπ : Function.Injective π) :
    (0 : K) ∉ (D.charPoly.map (algebraMap ℚ K)).roots := by
  intro h0
  have h := D.deg_X_eq_prod_roots (K := K)
  rw [Multiset.prod_eq_zero h0, Nat.cast_eq_zero] at h
  exact D.deg_X_ne_zero hπ h

end Roots

/-- (D3) for `1 - π^m`: `deg(1 - π^m) = #Ker(1 - π^m)` (here `p ≠ 1`, so `p ∤ 1`). -/
theorem card_ker_one_sub_X_pow (hp : p ≠ 1) (m : ℕ) (hm : 1 ≤ m) :
    D.deg (1 - X ^ m) = Nat.card (LinearMap.ker (aeval π (1 - X ^ m : ℤ[X]))) := by
  refine D.deg_eq_card_ker _ ?_
  rw [coeff_sub, coeff_one_zero, coeff_X_pow, if_neg (by omega), sub_zero]
  intro h
  exact hp (by exact_mod_cast Int.eq_one_of_dvd_one (Int.natCast_nonneg p) h)

/-- A6 applied: if `deg(1 - π^m) = ∏_i (1 - ω_i^m)` for all `m ≥ 1`, `|ω_i| = √q` with `q > 1` (RH) and
`π` is injective, then the complex roots of `P_π` are exactly the `ω_i`. -/
theorem roots_charPoly_eq (hπ : Function.Injective π) {q : ℝ} (hq : 1 < q) (ω : Multiset ℂ)
    (hω : ∀ w ∈ ω, ‖w‖ = Real.sqrt q)
    (h : ∀ m : ℕ, 1 ≤ m → (D.deg (1 - X ^ m) : ℂ) = (ω.map fun w => 1 - w ^ m).prod) :
    (D.charPoly.map (algebraMap ℚ ℂ)).roots = ω :=
  multiset_eq_of_prod_one_sub_pow_sqrt _ ω hq (D.zero_not_mem_roots hπ) hω
    (fun m hm => by rw [← D.deg_one_sub_X_pow, h m hm])

/-- CB2 over `ℂ`: `P_π = ∏_i (X - ω_i)`. -/
theorem charPoly_map_eq_prod (hπ : Function.Injective π) {q : ℝ} (hq : 1 < q) (ω : Multiset ℂ)
    (hω : ∀ w ∈ ω, ‖w‖ = Real.sqrt q)
    (h : ∀ m : ℕ, 1 ≤ m → (D.deg (1 - X ^ m) : ℂ) = (ω.map fun w => 1 - w ^ m).prod) :
    D.charPoly.map (algebraMap ℚ ℂ) = (ω.map fun w => X - C w).prod := by
  rw [← D.roots_charPoly_eq hπ hq ω hω h]
  exact (prod_multiset_X_sub_C_of_monic_of_roots_card_eq (D.charPoly_monic.map _)
    IsAlgClosed.card_roots_eq_natDegree).symm

end DegreeData

end RamanujanPetersson.JacAlg

end

-- ===== S4.Def_RP_JacAlg_Div =====
section

/-!
# Core B algebra, part 5: divisibility (unit S4-JacAlg, lemma L2 = route A1)

S4-CoreA writes `A[l^∞] ≃ (ℚ_l/ℤ_l)^s × Φ` with `Φ` finite and `l`-primary. Here `D` stands for the divisible
part and `Φ` for the finite part, both abstract:
* `card_tors_eq_mul`: `#(D × Φ)[n] = #D[n] * #Φ[n]` (through any `G ≃+ D × Φ`);
* `subsingleton_of_card_tors_eq`: if `#G[l] = #D[l]` (finite) and `Φ` is `l`-primary then `Φ = 0` (CB1);
* `DegreeData.card_tors`: `#A[n] = n^(2g)` for `p ∤ n` (the other half of A1, from (D2) + (D3)).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacAlg

open Polynomial

/-- The `n`-torsion `G[n]` of an additive group, as a type. -/
abbrev Tors (G : Type*) [AddCommGroup G] (n : ℕ) : Type _ := {x : G // n • x = 0}

/-- `(D × Φ)[n] ≃ D[n] × Φ[n]`. -/
def torsProdEquiv (D Φ : Type*) [AddCommGroup D] [AddCommGroup Φ] (n : ℕ) :
    Tors (D × Φ) n ≃ Tors D n × Tors Φ n where
  toFun x := (⟨x.1.1, by simpa using congrArg Prod.fst x.2⟩, ⟨x.1.2, by simpa using congrArg Prod.snd x.2⟩)
  invFun y := ⟨(y.1.1, y.2.1), by ext <;> simp [y.1.2, y.2.2]⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Torsion is carried along an additive isomorphism. -/
def torsCongr {G H : Type*} [AddCommGroup G] [AddCommGroup H] (e : G ≃+ H) (n : ℕ) :
    Tors G n ≃ Tors H n where
  toFun x := ⟨e x.1, by rw [← map_nsmul, x.2, map_zero]⟩
  invFun y := ⟨e.symm y.1, by rw [← map_nsmul, y.2, map_zero]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)

theorem card_tors_eq_mul {G D Φ : Type*} [AddCommGroup G] [AddCommGroup D] [AddCommGroup Φ]
    (e : G ≃+ D × Φ) (n : ℕ) :
    Nat.card (Tors G n) = Nat.card (Tors D n) * Nat.card (Tors Φ n) := by
  rw [Nat.card_congr ((torsCongr e n).trans (torsProdEquiv D Φ n)), Nat.card_prod]

/-- An `l`-primary group with no `l`-torsion is trivial. -/
theorem eq_zero_of_primary {Φ : Type*} [AddCommGroup Φ] (l : ℕ) (hΦ : ∀ x : Φ, ∃ k : ℕ, l ^ k • x = 0)
    (h : ∀ x : Φ, l • x = 0 → x = 0) (x : Φ) : x = 0 := by
  obtain ⟨k, hk⟩ := hΦ x
  induction k generalizing x with
  | zero => simpa using hk
  | succ k ih =>
    rw [pow_succ, ← smul_smul] at hk
    exact h x (ih (l • x) hk)

/-- A1 / CB1: if `G ≃+ D × Φ` with `Φ` `l`-primary and `#G[l] = #D[l]` finite, then `Φ = 0`. -/
theorem subsingleton_of_card_tors_eq {G D Φ : Type*} [AddCommGroup G] [AddCommGroup D] [AddCommGroup Φ]
    (e : G ≃+ D × Φ) (l : ℕ) (hΦ : ∀ x : Φ, ∃ k : ℕ, l ^ k • x = 0) [Finite (Tors D l)]
    (h : Nat.card (Tors G l) = Nat.card (Tors D l)) : Subsingleton Φ := by
  have hD : 0 < Nat.card (Tors D l) := by
    have : Nonempty (Tors D l) := ⟨⟨0, smul_zero _⟩⟩
    exact Nat.card_pos
  rw [card_tors_eq_mul e, Nat.mul_eq_left hD.ne'] at h
  have hu : Subsingleton (Tors Φ l) := (Nat.card_eq_one_iff_unique.mp h).1
  have h0 : ∀ x : Φ, l • x = 0 → x = 0 := fun x hx =>
    congrArg Subtype.val (hu.elim (⟨x, hx⟩ : Tors Φ l) ⟨0, smul_zero _⟩)
  exact ⟨fun a b => by rw [eq_zero_of_primary l hΦ h0 a, eq_zero_of_primary l hΦ h0 b]⟩

namespace DegreeData

variable {A : Type*} [AddCommGroup A] {π : Module.End ℤ A} {g p : ℕ} (D : DegreeData π g p)

include D in
/-- `#A[n] = n^(2g)` for `p ∤ n` (A1, first half, as torsion of `A`). -/
theorem card_tors (n : ℕ) (hn : ¬ (p : ℤ) ∣ n) : Nat.card (Tors A n) = n ^ (2 * g) := by
  rw [← D.card_ker_natCast n hn]
  exact Nat.card_congr
    { toFun := fun x => ⟨x.1, (mem_ker_natCast (π := π) n x.1).mpr x.2⟩
      invFun := fun y => ⟨y.1, (mem_ker_natCast (π := π) n y.1).mp y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end DegreeData

end RamanujanPetersson.JacAlg

end

-- ===== S4.Def_RP_JacAlg_Charpoly =====
section

/-!
# Core B algebra, part 8: `P_π = charpoly(T_l π)` (unit S4-JacAlg, L4/L5 = Milne 10.20-10.22, steps C1, C2)

* C1 `norm_resultant_eq_of_int`, `norm_resultant_eq_of_int_rat`: for monic `P, Q` over `ℤ_l`, equal norms
  `‖Res(P, F)‖ = ‖Res(Q, F)‖` for all integer `F` with `p ∤ F(0)` (`p ≠ l` prime) extend to all `G` over `ℤ_l`
  (approximation mod `l^K`) and then over `ℚ_l` (clearing denominators; the degrees agree via `F = l`).
* C2 `charpoly_eq_of_norm_det`: if `‖Res(P₀, F)‖_l = ‖det F(M)‖_l` for those `F`, then `charpoly M = P₀`.
  `DegreeData.deg_eq_resultant`: `deg F = Res(P₀, F)` when `P_π = P₀` (Milne 10.22).
  `DegreeData.charpoly_eq`: `‖deg F‖_l = ‖det F(M)‖_l` for `p ∤ F(0)` gives `charpoly(M) = P_π` (Milne 10.20),
  and `DegreeData.finrank_eq`: the rank is `2g`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacAlg

open Polynomial

variable {l : ℕ} [hl : Fact l.Prime]

lemma norm_sub_le_of_toZModPow_eq {x y : ℤ_[l]} {K : ℕ}
    (h : PadicInt.toZModPow K x = PadicInt.toZModPow K y) : ‖x - y‖ ≤ (l : ℝ) ^ (-(K : ℤ)) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, h,
    sub_self]

lemma not_dvd_of_prime_ne {p : ℕ} (hp : p.Prime) (hpl : p ≠ l) (K : ℕ) : ¬ (p : ℤ) ∣ (l : ℤ) ^ K := by
  intro h
  have h2 : p ∣ l ^ K := by exact_mod_cast h
  exact hpl ((Nat.prime_dvd_prime_iff_eq hp hl.out).mp (hp.dvd_of_dvd_pow h2))

lemma exists_int_approx {p : ℕ} (hp : p.Prime) (hpl : p ≠ l) (G : ℤ_[l][X]) (K : ℕ) :
    ∃ F : ℤ[X], ¬ (p : ℤ) ∣ F.coeff 0 ∧ F.natDegree ≤ G.natDegree ∧
      (F.map (Int.castRingHom ℤ_[l])).map (PadicInt.toZModPow K) = G.map (PadicInt.toZModPow K) := by
  have hsurj : Function.Surjective (Int.castRingHom (ZMod (l ^ K))) := ZMod.intCast_surjective
  obtain ⟨F₀, hF₀, hdeg⟩ := exists_natDegree_eq_of_mem_lifts
    (mem_lifts_of_surjective hsurj (G.map (PadicInt.toZModPow K)))
  have hcomp : (PadicInt.toZModPow K).comp (Int.castRingHom ℤ_[l]) = Int.castRingHom (ZMod (l ^ K)) :=
    RingHom.ext_int _ _
  have hdeg' : F₀.natDegree ≤ G.natDegree := by rw [hdeg]; exact natDegree_map_le
  by_cases h0 : (p : ℤ) ∣ F₀.coeff 0
  · refine ⟨F₀ + C ((l : ℤ) ^ K), ?_, ?_, ?_⟩
    · rw [coeff_add, coeff_C_zero]
      intro h
      exact not_dvd_of_prime_ne hp hpl K ((dvd_add_right h0).mp h)
    · exact natDegree_add_C.le.trans hdeg'
    · have hz : (Int.castRingHom (ZMod (l ^ K))) ((l : ℤ) ^ K) = 0 := by
        rw [map_pow, map_natCast]; exact_mod_cast ZMod.natCast_self (l ^ K)
      rw [Polynomial.map_map, hcomp, Polynomial.map_add, hF₀, map_C, hz, C_0, add_zero]
  · refine ⟨F₀, h0, hdeg', ?_⟩
    rw [Polynomial.map_map, hcomp, hF₀]

lemma norm_resultant_le_of_int {p : ℕ} (hp : p.Prime) (hpl : p ≠ l) {P Q : ℤ_[l][X]} (hP : P.Monic)
    (hQ : Q.Monic) (H : ∀ F : ℤ[X], ¬ (p : ℤ) ∣ F.coeff 0 →
      ‖resultant P (F.map (Int.castRingHom ℤ_[l]))‖ = ‖resultant Q (F.map (Int.castRingHom ℤ_[l]))‖)
    (G : ℤ_[l][X]) : ‖resultant P G‖ ≤ ‖resultant Q G‖ := by
  have hK : ∀ K : ℕ, ‖resultant P G‖ ≤ max ((l : ℝ) ^ (-(K : ℤ))) ‖resultant Q G‖ := by
    intro K
    obtain ⟨F, hF0, hFdeg, hFmod⟩ := exists_int_approx hp hpl G K
    have HF := H F hF0
    obtain ⟨Fl, hFl_def⟩ : ∃ Fl, Fl = F.map (Int.castRingHom ℤ_[l]) := ⟨_, rfl⟩
    rw [← hFl_def] at HF hFmod
    have hFl : Fl.natDegree ≤ G.natDegree := hFl_def ▸ natDegree_map_le.trans hFdeg
    have hc : ∀ S : ℤ_[l][X], S.Monic →
        ‖resultant S G - resultant S Fl‖ ≤ (l : ℝ) ^ (-(K : ℤ)) := by
      intro S hS
      rw [← resultant_monic_eq hS hFl]
      apply norm_sub_le_of_toZModPow_eq
      rw [← resultant_map_map, ← resultant_map_map, hFmod]
    have h1 := PadicInt.nonarchimedean (resultant P G - resultant P Fl) (resultant P Fl)
    have h2 := PadicInt.nonarchimedean (resultant Q Fl - resultant Q G) (resultant Q G)
    rw [sub_add_cancel] at h1 h2
    rw [norm_sub_rev] at h2
    rw [HF] at h1
    calc ‖resultant P G‖ ≤ max ‖resultant P G - resultant P Fl‖ ‖resultant Q Fl‖ := h1
      _ ≤ max ((l : ℝ) ^ (-(K : ℤ))) (max ((l : ℝ) ^ (-(K : ℤ))) ‖resultant Q G‖) :=
          max_le_max (hc P hP) (h2.trans (max_le_max (hc Q hQ) le_rfl))
      _ = max ((l : ℝ) ^ (-(K : ℤ))) ‖resultant Q G‖ := by rw [← max_assoc, max_self]
  by_contra hlt
  rw [not_le] at hlt
  have hpos : 0 < ‖resultant P G‖ := (norm_nonneg _).trans_lt hlt
  obtain ⟨K, hK'⟩ : ∃ K : ℕ, (l : ℝ) ^ (-(K : ℤ)) < ‖resultant P G‖ := by
    have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
    obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ hl1)
    refine ⟨K, ?_⟩
    rwa [zpow_neg, zpow_natCast, ← inv_pow]
  exact absurd (hK K) (not_le.mpr (max_lt hK' hlt))

/-- **C1 over `ℤ_l`.** -/
theorem norm_resultant_eq_of_int {p : ℕ} (hp : p.Prime) (hpl : p ≠ l) {P Q : ℤ_[l][X]} (hP : P.Monic)
    (hQ : Q.Monic) (H : ∀ F : ℤ[X], ¬ (p : ℤ) ∣ F.coeff 0 →
      ‖resultant P (F.map (Int.castRingHom ℤ_[l]))‖ = ‖resultant Q (F.map (Int.castRingHom ℤ_[l]))‖)
    (G : ℤ_[l][X]) : ‖resultant P G‖ = ‖resultant Q G‖ :=
  le_antisymm (norm_resultant_le_of_int hp hpl hP hQ H G)
    (norm_resultant_le_of_int hp hpl hQ hP (fun F hF => (H F hF).symm) G)

/-- **C1 over `ℚ_l`.** -/
theorem norm_resultant_eq_of_int_rat {p : ℕ} (hp : p.Prime) (hpl : p ≠ l) {P Q : ℤ_[l][X]}
    (hP : P.Monic) (hQ : Q.Monic) (H : ∀ F : ℤ[X], ¬ (p : ℤ) ∣ F.coeff 0 →
      ‖resultant P (F.map (Int.castRingHom ℤ_[l]))‖ = ‖resultant Q (F.map (Int.castRingHom ℤ_[l]))‖)
    (G : ℚ_[l][X]) :
    ‖resultant (P.map (algebraMap ℤ_[l] ℚ_[l])) G‖ = ‖resultant (Q.map (algebraMap ℤ_[l] ℚ_[l])) G‖ := by
  have hι : Function.Injective (algebraMap ℤ_[l] ℚ_[l]) := IsFractionRing.injective ℤ_[l] ℚ_[l]
  have hnorm : ∀ x : ℤ_[l], ‖algebraMap ℤ_[l] ℚ_[l] x‖ = ‖x‖ := fun x => by
    rw [PadicInt.algebraMap_apply, PadicInt.norm_def]
  -- equal degrees, from `F = l`
  have hdeg : P.natDegree = Q.natDegree := by
    have h := norm_resultant_eq_of_int hp hpl hP hQ H (C (l : ℤ_[l]))
    rw [resultant_C_right, resultant_C_right, hP.coeff_natDegree, hQ.coeff_natDegree, one_pow, one_mul,
      one_mul, norm_pow, norm_pow, PadicInt.norm_p] at h
    have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
    exact pow_right_injective₀ (inv_pos.mpr (zero_lt_one.trans hl1)) (inv_lt_one_of_one_lt₀ hl1).ne h
  -- clear denominators
  obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_map_to_map (M := nonZeroDivisors ℤ_[l])
    (S := ℚ_[l]) G
  generalize IsLocalization.integerNormalization (nonZeroDivisors ℤ_[l]) G = G' at hb
  have hb0 : algebraMap ℤ_[l] ℚ_[l] b ≠ 0 :=
    (map_ne_zero_iff _ hι).mpr (nonZeroDivisors.coe_ne_zero b)
  have hG' : G'.map (algebraMap ℤ_[l] ℚ_[l]) = C (algebraMap ℤ_[l] ℚ_[l] b) * G := by
    rw [hb, ← algebraMap_smul ℚ_[l] (b : ℤ_[l]) G, smul_eq_C_mul]
  have key : ∀ S : ℤ_[l][X], ‖resultant S G'‖ =
      ‖algebraMap ℤ_[l] ℚ_[l] b‖ ^ S.natDegree * ‖resultant (S.map (algebraMap ℤ_[l] ℚ_[l])) G‖ := by
    intro S
    have e1 : resultant (S.map (algebraMap ℤ_[l] ℚ_[l])) (G'.map (algebraMap ℤ_[l] ℚ_[l])) =
        algebraMap ℤ_[l] ℚ_[l] (resultant S G') := by
      rw [natDegree_map_eq_of_injective hι, natDegree_map_eq_of_injective hι, resultant_map_map]
    have e2 : resultant (S.map (algebraMap ℤ_[l] ℚ_[l])) (G'.map (algebraMap ℤ_[l] ℚ_[l])) =
        (algebraMap ℤ_[l] ℚ_[l] b) ^ S.natDegree * resultant (S.map (algebraMap ℤ_[l] ℚ_[l])) G := by
      rw [hG', natDegree_C_mul hb0, resultant_C_mul_right, natDegree_map_eq_of_injective hι]
    rw [← hnorm, ← e1, e2, norm_mul, norm_pow]
  have h := norm_resultant_eq_of_int hp hpl hP hQ H G'
  rw [key, key, hdeg] at h
  exact mul_left_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.mpr hb0)) h

/-- **C2 (core).** If `‖Res(P₀, F)‖_l = ‖det F(M)‖_l` for every integer `F` with `p ∤ F(0)`, then
`charpoly M = P₀` over `ℤ_l`. -/
theorem charpoly_eq_of_norm_det {p : ℕ} (hp : p.Prime) (hpl : p ≠ l) {P0 : ℤ[X]} (hP0 : P0.Monic)
    {T : Type*} [AddCommGroup T] [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T]
    (M : Module.End ℤ_[l] T)
    (hkey : ∀ F : ℤ[X], ¬ (p : ℤ) ∣ F.coeff 0 →
      ‖((resultant P0 F : ℤ) : ℤ_[l])‖ = ‖LinearMap.det (aeval M (F.map (Int.castRingHom ℤ_[l])))‖) :
    M.charpoly = P0.map (Int.castRingHom ℤ_[l]) := by
  have hι : Function.Injective (algebraMap ℤ_[l] ℚ_[l]) := IsFractionRing.injective ℤ_[l] ℚ_[l]
  have hz : Function.Injective (Int.castRingHom ℤ_[l]) := (Int.castRingHom ℤ_[l]).injective_int
  have hχ : M.charpoly.Monic := LinearMap.charpoly_monic M
  have hP : (P0.map (Int.castRingHom ℤ_[l])).Monic := hP0.map _
  have H : ∀ F : ℤ[X], ¬ (p : ℤ) ∣ F.coeff 0 →
      ‖resultant (P0.map (Int.castRingHom ℤ_[l])) (F.map (Int.castRingHom ℤ_[l]))‖ =
        ‖resultant M.charpoly (F.map (Int.castRingHom ℤ_[l]))‖ := by
    intro F hF
    have h := hkey F hF
    rw [linearMap_det_aeval_eq_resultant, ← LinearMap.charpoly_natDegree M] at h
    rw [← h, natDegree_map_eq_of_injective hz, natDegree_map_eq_of_injective hz, resultant_map_map,
      eq_intCast]
  have heq := eq_of_norm_resultant_eq (hP.map _) (hχ.map _) (norm_resultant_eq_of_int_rat hp hpl hP hχ H)
  exact (Polynomial.map_injective _ hι heq).symm

namespace DegreeData

variable {A : Type*} [AddCommGroup A] {π : Module.End ℤ A} {g p : ℕ} (D : DegreeData π g p)

/-- Milne 10.22 in resultant form: `deg F = Res(P₀, F)` when `P_π = P₀ ∈ ℤ[X]`. -/
theorem deg_eq_resultant {P0 : ℤ[X]} (hP0 : D.charPoly = P0.map (Int.castRingHom ℚ)) (F : ℤ[X]) :
    (D.deg F : ℤ) = resultant P0 F := by
  have hinj : Function.Injective (Int.castRingHom ℂ) := (Int.castRingHom ℂ).injective_int
  have hmono : P0.Monic := monic_of_injective (Int.castRingHom ℚ).injective_int (hP0 ▸ D.charPoly_monic)
  have hmap : D.charPoly.map (algebraMap ℚ ℂ) = P0.map (Int.castRingHom ℂ) := by
    rw [hP0, Polynomial.map_map]
    congr 1
  have h1 := D.deg_eq_prod_roots (K := ℂ) F
  rw [hmap] at h1
  have h2 := resultant_eq_prod_eval (P0.map (Int.castRingHom ℂ)) (F.map (Int.castRingHom ℂ)) F.natDegree
    natDegree_map_le (IsAlgClosed.splits _)
  rw [(hmono.map _).leadingCoeff, one_pow, one_mul, natDegree_map_eq_of_injective hinj,
    resultant_map_map] at h2
  apply Int.cast_injective (α := ℂ)
  rw [Int.cast_natCast]
  exact h1.trans (h2.symm.trans (eq_intCast _ _))

/-- **Milne 10.20 / route A4.** `charpoly(M) = P_π` over `ℤ_l` when `‖deg F‖_l = ‖det F(M)‖_l` for every
integer `F` with `p ∤ F(0)` (`p ≠ l` prime) and `P_π = P₀ ∈ ℤ[X]`. -/
theorem charpoly_eq (hp : p.Prime) (hpl : p ≠ l) {P0 : ℤ[X]}
    (hP0 : D.charPoly = P0.map (Int.castRingHom ℚ)) {T : Type*} [AddCommGroup T] [Module ℤ_[l] T]
    [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] (M : Module.End ℤ_[l] T)
    (hkey : ∀ F : ℤ[X], ¬ (p : ℤ) ∣ F.coeff 0 →
      ‖((D.deg F : ℕ) : ℤ_[l])‖ = ‖LinearMap.det (aeval M (F.map (Int.castRingHom ℤ_[l])))‖) :
    M.charpoly = P0.map (Int.castRingHom ℤ_[l]) := by
  have hmono : P0.Monic := monic_of_injective (Int.castRingHom ℚ).injective_int (hP0 ▸ D.charPoly_monic)
  refine charpoly_eq_of_norm_det hp hpl hmono M fun F hF => ?_
  rw [← D.deg_eq_resultant hP0 F, Int.cast_natCast]
  exact hkey F hF

theorem finrank_eq (hp : p.Prime) (hpl : p ≠ l) {P0 : ℤ[X]}
    (hP0 : D.charPoly = P0.map (Int.castRingHom ℚ)) {T : Type*} [AddCommGroup T] [Module ℤ_[l] T]
    [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] (M : Module.End ℤ_[l] T)
    (hkey : ∀ F : ℤ[X], ¬ (p : ℤ) ∣ F.coeff 0 →
      ‖((D.deg F : ℕ) : ℤ_[l])‖ = ‖LinearMap.det (aeval M (F.map (Int.castRingHom ℤ_[l])))‖) :
    Module.finrank ℤ_[l] T = 2 * g := by
  rw [← LinearMap.charpoly_natDegree M, D.charpoly_eq hp hpl hP0 M hkey,
    natDegree_map_eq_of_injective (Int.castRingHom ℤ_[l]).injective_int, ← D.charPoly_natDegree, hP0,
    natDegree_map_eq_of_injective (Int.castRingHom ℚ).injective_int]

end DegreeData

end RamanujanPetersson.JacAlg

end

-- ===== S4.Def_RP_JacAlg =====
section

/-!
# Core B algebra (unit S4-JacAlg, route S4_COREB_ROUTE.md section 3, lemmas L1-L7)

Umbrella file. Namespace `RamanujanPetersson.JacAlg`.
* L1 `DegreeData π g p` (Defs): the interface every geometric Core B unit targets; `charPoly` = `P_π`.
* L5'/L6 (Norm, Milne 10.22): `DegreeData.charPoly_monic`, `charPoly_natDegree`, `deg_eq_prod_roots`.
* L7 (Multiset): `multiset_eq_of_prod_one_sub_pow(_sqrt)`.
* A5/A6 (Zeta): `deg_one_sub_X_pow`, `card_ker_one_sub_X_pow`, `roots_charPoly_eq`, `charPoly_map_eq_prod`.
* L2 (Div): `subsingleton_of_card_tors_eq`, `DegreeData.card_tors`.
* L3 (Kernel): `card_quotient_range`, `card_ker_mod`.
* L4 (Res, Milne 10.21): `det_aeval_eq_resultant`, `linearMap_det_aeval_eq_resultant`, `eq_of_norm_resultant_eq`.
* L4/L5 (Charpoly, Milne 10.20): `charpoly_eq_of_norm_det`, `DegreeData.deg_eq_resultant`,
  `DegreeData.charpoly_eq`, `DegreeData.finrank_eq`.
-/

end


