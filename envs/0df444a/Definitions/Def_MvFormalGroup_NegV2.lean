-- Prove2me | Definitions.Def_MvFormalGroup_NegV2
-- name    : MvFormalGroup_NegV2
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/609b0452-509f-5de6-895b-5303189539f9
-- title:
--   Negation and inversion for multivariate formal group laws
-- statement:
--   Throughout, $F$ is a $g$-dimensional formal group law over a commutative ring $R$, presented by a family `F.toPowerSeries : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R` with vanishing constant terms, prescribed linear coefficients $\delta$ in each group of variables, and the associativity identity; `IsComm F` is the commutativity hypothesis. For a family $a = (a_1,\dots ,a_g)$ of power series in variables indexed by an arbitrary type $\tau$, all with zero constant term, `negApprox F a` is the sequence of successive approximations to the inverse of $a$: it starts at $0$ and passes from $y^{(n)}$ to $y^{(n+1)}_i = y^{(n)}_i - H_{n+1}\bigl(F_i(a,y^{(n)})\bigr)$, where $H_{n+1}$ takes the homogeneous component of total degree $n+1$. The coefficients of $y^{(n)}$ in multidegrees of degree $\le n$ no longer change with $n$, and `negSeries F a` is the family obtained by reading off, for each multi-index $d$, the $d$-th coefficient of $y^{(\deg d)}$. It has zero constant terms, satisfies $F_i(a,\ominus a)=0$ and $F_i(\ominus a,a)=0$, is the unique such family on either side, has linear coefficients the negatives of those of $a$, commutes with substitution of series with zero constant term, and for commutative $F$ converts the formal sum of $a$ and $b$ into the formal sum of their inverses. `invSeries F` is $\ominus$ applied to the family of variables $X_i$, the inversion series of $F$, of linear part $-1$.
--
--   On this basis, for commutative $G$ the negation `Hom.neg` of a homomorphism $F \to G$ is the family $\ominus_G \varphi$, shown to satisfy the defining substitution identity of a homomorphism; this upgrades the additive commutative monoid of homomorphisms to an additive commutative group, and `End F` from a semiring to a ring, with $\varphi - \psi$ given by $G(\varphi, \ominus\psi)$, with $-1$ corresponding to `invSeries F` (also named `invHom F`), with the integer multiples $[n]$ and $[-(n+1)]$ identified as `F.nthSeries n` and $\ominus(\mathrm{F.nthSeries}(n+1))$, and with the linear-part ring homomorphism sending $n \in \mathbb{Z}$ to $n \cdot 1$. The preparatory sections supply the coefficient estimates used in the degreewise construction: comparison of coefficients of powers, of finitely supported products of powers and of substitutions under agreement up to a degree bound, vanishing of low-degree coefficients of such products, the unit laws $F_i(a,0) = a_i = F_i(0,a)$ for arbitrary admissible families, and the statement that subtracting a family $E$ homogeneous of degree exactly $N$ from the second argument of $F$ alters the coefficients in degrees $\le N$ by precisely $-E_i$.
--
--   **Relation to Mathlib.** The power-series substitution calculus used here (`MvPowerSeries`, `subst`, `HasSubst`, `homogeneousComponent`, `order`) is Mathlib's; the formal group law structure, its homomorphisms and endomorphism ring, and the inverse series constructed degreewise are the project's own.
--
--   **Where it is used.** These definitions are part of the formal-group infrastructure on which the study of torsion and of $p$-divisible towers attached to a formal group over a base ring rests, the setting in which the local conditions at $p$ in the deformation-theoretic part of the modularity argument are formulated.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_MvFormalGroup_NegV2.lean

import Definitions.Def_MvFormalGroup_EndRingV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {g h k : ℕ} {R : Type*} [CommRing R]

section Congr

variable {τ : Type*}

theorem coeff_pow_congr {c c' : MvPowerSeries τ R} {n : ℕ}
    (h : ∀ e : τ →₀ ℕ, e.degree ≤ n → coeff e c = coeff e c') {k : ℕ}
    {d : τ →₀ ℕ} (hd : d.degree ≤ n) :
    coeff d (c ^ k) = coeff d (c' ^ k) := by
  classical
  induction k generalizing d with
  | zero => rfl
  | succ k IH =>
    rw [pow_succ, pow_succ, coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have h1 : p.1.degree ≤ n := by
      refine le_trans ?_ hd
      rw [← hp, map_add]
      exact Nat.le_add_right _ _
    have h2 : p.2.degree ≤ n := by
      refine le_trans ?_ hd
      rw [← hp, map_add]
      exact Nat.le_add_left _ _
    rw [IH h1, h p.2 h2]

theorem coeff_finsuppProd_pow_congr {σ' : Type*} {c c' : σ' → MvPowerSeries τ R} {n : ℕ}
    (h : ∀ j, ∀ e : τ →₀ ℕ, e.degree ≤ n → coeff e (c j) = coeff e (c' j))
    (m : σ' →₀ ℕ) {d : τ →₀ ℕ} (hd : d.degree ≤ n) :
    coeff d (m.prod fun j l => c j ^ l) = coeff d (m.prod fun j l => c' j ^ l) := by
  classical
  induction m using Finsupp.induction generalizing d with
  | zero => simp
  | single_add j l m hjm hl IH =>
    rw [Finsupp.prod_add_index (fun _ _ => pow_zero _) (fun _ _ _ _ => pow_add _ _ _),
      Finsupp.prod_add_index (fun _ _ => pow_zero _) (fun _ _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (h := fun j' l' => c j' ^ l') (pow_zero _),
      Finsupp.prod_single_index (h := fun j' l' => c' j' ^ l') (pow_zero _),
      coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have h1 : p.1.degree ≤ n := by
      refine le_trans ?_ hd
      rw [← hp, map_add]
      exact Nat.le_add_right _ _
    have h2 : p.2.degree ≤ n := by
      refine le_trans ?_ hd
      rw [← hp, map_add]
      exact Nat.le_add_left _ _
    rw [coeff_pow_congr (h j) h1, IH h2]

theorem coeff_subst_congr {σ' : Type*} [Finite σ'] {c c' : σ' → MvPowerSeries τ R}
    (hc : ∀ j, (c j).constantCoeff = 0) (hc' : ∀ j, (c' j).constantCoeff = 0) {n : ℕ}
    (h : ∀ j, ∀ e : τ →₀ ℕ, e.degree ≤ n → coeff e (c j) = coeff e (c' j))
    (f : MvPowerSeries σ' R) {d : τ →₀ ℕ} (hd : d.degree ≤ n) :
    coeff d (subst c f) = coeff d (subst c' f) := by
  rw [coeff_subst (hasSubst_of_constantCoeff_zero hc),
    coeff_subst (hasSubst_of_constantCoeff_zero hc')]
  exact finsum_congr fun m => by
    rw [coeff_finsuppProd_pow_congr h m hd]

end Congr

section Vanish

variable {τ : Type*}

theorem coeff_pow_eq_zero_of_degree_lt {c : MvPowerSeries τ R}
    (hc : c.constantCoeff = 0) {l : ℕ} {d : τ →₀ ℕ} (hd : d.degree < l) :
    coeff d (c ^ l) = 0 := by
  classical
  induction l generalizing d with
  | zero => omega
  | succ l IH =>
    rw [pow_succ, coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    by_cases h1 : p.1.degree < l
    · rw [IH h1, zero_mul]
    · have h2 : p.2 = 0 := by
        by_contra h2
        have : 1 ≤ p.2.degree := by
          rcases Nat.eq_zero_or_pos p.2.degree with hz | hpos
          · exact absurd ((Finsupp.degree_eq_zero_iff p.2).mp hz) h2
          · exact hpos
        have hdd : p.1.degree + p.2.degree = d.degree := by
          rw [← hp, map_add]
        omega
      rw [h2, coeff_zero_eq_constantCoeff_apply, hc, mul_zero]

theorem coeff_finsuppProd_pow_eq_zero_of_degree_lt {σ' : Type*}
    {c : σ' → MvPowerSeries τ R} (hc : ∀ j, (c j).constantCoeff = 0)
    {m : σ' →₀ ℕ} {d : τ →₀ ℕ} (hd : d.degree < m.degree) :
    coeff d (m.prod fun j l => c j ^ l) = 0 := by
  classical
  induction m using Finsupp.induction generalizing d with
  | zero =>
    rw [(Finsupp.degree_eq_zero_iff (0 : σ' →₀ ℕ)).mpr rfl] at hd
    omega
  | single_add j l m hjm hl IH =>
    rw [Finsupp.prod_add_index (fun _ _ => pow_zero _) (fun _ _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (h := fun j' l' => c j' ^ l') (pow_zero _), coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hdd : p.1.degree + p.2.degree = d.degree := by
      rw [← hp, map_add]
    have hsum : (Finsupp.single j l + m).degree = l + m.degree := by
      rw [map_add, Finsupp.degree_single]
    by_cases h1 : p.1.degree < l
    · rw [coeff_pow_eq_zero_of_degree_lt (hc j) h1, zero_mul]
    · have h2 : p.2.degree < m.degree := by omega
      rw [IH h2, mul_zero]

end Vanish

section SubCongr

variable {τ : Type*}

theorem coeff_mul_congr_right {u c c' : MvPowerSeries τ R} {K r : ℕ}
    (hu : ∀ e : τ →₀ ℕ, e.degree < r → coeff e u = 0)
    (hcc : ∀ e : τ →₀ ℕ, e.degree ≤ K → coeff e c = coeff e c')
    {d : τ →₀ ℕ} (hd : d.degree ≤ K + r) :
    coeff d (u * c) = coeff d (u * c') := by
  classical
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hdd : p.1.degree + p.2.degree = d.degree := by
    rw [← hp, map_add]
  by_cases h1 : p.1.degree < r
  · rw [hu p.1 h1, zero_mul, zero_mul]
  · rw [hcc p.2 (by omega)]

theorem coeff_pow_sub_congr {c c' : MvPowerSeries τ R} {N : ℕ} (hN : 1 ≤ N)
    (hc : c.constantCoeff = 0) (hc' : c'.constantCoeff = 0)
    (hcc : ∀ e : τ →₀ ℕ, e.degree < N → coeff e c = coeff e c') {l : ℕ}
    {d : τ →₀ ℕ} (hd : d.degree ≤ N + l - 2) :
    coeff d (c ^ l) = coeff d (c' ^ l) := by
  classical
  induction l generalizing d with
  | zero => rw [pow_zero, pow_zero]
  | succ l IH =>
    rcases Nat.eq_zero_or_pos l with hl0 | hlpos
    · subst hl0
      rw [pow_one, pow_one]
      exact hcc d (by omega)
    · have step1 : coeff d (c ^ (l + 1)) = coeff d (c ^ l * c') := by
        rw [pow_succ]
        have hvanish : ∀ e : τ →₀ ℕ, e.degree < l → coeff e (c ^ l) = 0 :=
          fun e he => coeff_pow_eq_zero_of_degree_lt hc he
        exact coeff_mul_congr_right (K := N - 1) (r := l) hvanish
          (fun e he => hcc e (by omega)) (by omega)
      have step2 : coeff d (c ^ l * c') = coeff d (c' ^ l * c') := by
        rw [mul_comm (c ^ l) c', mul_comm (c' ^ l) c']
        have hvanish : ∀ e : τ →₀ ℕ, e.degree < 1 → coeff e c' = 0 := by
          intro e he
          have he0 : e = 0 := by
            rcases Nat.eq_zero_or_pos e.degree with hz | hpos
            · exact (Finsupp.degree_eq_zero_iff e).mp hz
            · omega
          subst he0
          rw [coeff_zero_eq_constantCoeff_apply, hc']
        exact coeff_mul_congr_right (K := N + l - 2) (r := 1) hvanish
          (fun e he => IH he) (by omega)
      rw [step1, step2, ← pow_succ]

theorem coeff_finsuppProd_pow_sub_congr {σ' : Type*} {c c' : σ' → MvPowerSeries τ R}
    {N : ℕ} (hN : 1 ≤ N)
    (hc : ∀ j, (c j).constantCoeff = 0) (hc' : ∀ j, (c' j).constantCoeff = 0)
    (hcc : ∀ j, ∀ e : τ →₀ ℕ, e.degree < N → coeff e (c j) = coeff e (c' j))
    {m : σ' →₀ ℕ} {d : τ →₀ ℕ} (hd : d.degree ≤ N + m.degree - 2) :
    coeff d (m.prod fun j l => c j ^ l) = coeff d (m.prod fun j l => c' j ^ l) := by
  classical
  induction m using Finsupp.induction generalizing d with
  | zero => rw [Finsupp.prod_zero_index, Finsupp.prod_zero_index]
  | single_add j l m hjm hl IH =>
    have hsum : (Finsupp.single j l + m).degree = l + m.degree := by
      rw [map_add, Finsupp.degree_single]
    rw [hsum] at hd
    rw [Finsupp.prod_add_index (fun _ _ => pow_zero _) (fun _ _ _ _ => pow_add _ _ _),
      Finsupp.prod_add_index (fun _ _ => pow_zero _) (fun _ _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (h := fun j' l' => c j' ^ l') (pow_zero _),
      Finsupp.prod_single_index (h := fun j' l' => c' j' ^ l') (pow_zero _)]
    have step1 : coeff d ((c j) ^ l * m.prod fun j' l' => c j' ^ l')
        = coeff d ((c' j) ^ l * m.prod fun j' l' => c j' ^ l') := by
      rw [mul_comm ((c j) ^ l) _, mul_comm ((c' j) ^ l) _]
      have hvanish : ∀ e : τ →₀ ℕ, e.degree < m.degree →
          coeff e (m.prod fun j' l' => c j' ^ l') = 0 :=
        fun e he => coeff_finsuppProd_pow_eq_zero_of_degree_lt hc he
      exact coeff_mul_congr_right (K := N + l - 2) (r := m.degree) hvanish
        (fun e he => coeff_pow_sub_congr hN (hc j) (hc' j) (hcc j) he) (by omega)
    have step2 : coeff d ((c' j) ^ l * m.prod fun j' l' => c j' ^ l')
        = coeff d ((c' j) ^ l * m.prod fun j' l' => c' j' ^ l') := by
      have hvanish : ∀ e : τ →₀ ℕ, e.degree < l → coeff e ((c' j) ^ l) = 0 :=
        fun e he => coeff_pow_eq_zero_of_degree_lt (hc' j) he
      exact coeff_mul_congr_right (K := N + m.degree - 2) (r := l) hvanish
        (fun e he => IH he) (by omega)
    rw [step1, step2]

end SubCongr

section UnitGeneral

variable {τ : Type*} (F : MvFormalGroup g R)

theorem subst_elim_zero_right {a : Fin g → MvPowerSeries τ R}
    (ha : ∀ j, (a j).constantCoeff = 0) (i : Fin g) :
    subst (Sum.elim a fun _ => 0) (F.toPowerSeries i) = a i := by
  have hsa : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have hX0 : HasSubst (Sum.elim (fun j => (X j : MvPowerSeries (Fin g) R))
      (fun _ => 0) : Fin g ⊕ Fin g → MvPowerSeries (Fin g) R) :=
    hasSubst_elim (fun j => constantCoeff_X j) fun _ => map_zero _
  have hfam : (fun s : Fin g ⊕ Fin g => subst a
      ((Sum.elim (fun j => (X j : MvPowerSeries (Fin g) R))
        (fun _ => 0) : Fin g ⊕ Fin g → MvPowerSeries (Fin g) R) s))
      = (Sum.elim a (fun _ => 0) : Fin g ⊕ Fin g → MvPowerSeries τ R) := by
    funext s
    rcases s with j | j
    · show subst a (X j) = a j
      exact subst_X hsa j
    · show subst a (0 : MvPowerSeries (Fin g) R) = 0
      rw [← coe_substAlgHom hsa, map_zero]
  rw [← hfam, ← subst_comp_subst_apply hX0 hsa, subst_elim_X_zero F i, subst_X hsa]

theorem subst_elim_zero_left {a : Fin g → MvPowerSeries τ R}
    (ha : ∀ j, (a j).constantCoeff = 0) (i : Fin g) :
    subst (Sum.elim (fun _ => 0) a) (F.toPowerSeries i) = a i := by
  have hsa : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have h0X : HasSubst (Sum.elim (fun _ => 0)
      (fun j => (X j : MvPowerSeries (Fin g) R)) : Fin g ⊕ Fin g → MvPowerSeries (Fin g) R) :=
    hasSubst_elim (fun _ => map_zero _) fun j => constantCoeff_X j
  have hfam : (fun s : Fin g ⊕ Fin g => subst a
      ((Sum.elim (fun _ => 0)
        (fun j => (X j : MvPowerSeries (Fin g) R)) : Fin g ⊕ Fin g → MvPowerSeries (Fin g) R) s))
      = (Sum.elim (fun _ => 0) a : Fin g ⊕ Fin g → MvPowerSeries τ R) := by
    funext s
    rcases s with j | j
    · show subst a (0 : MvPowerSeries (Fin g) R) = 0
      rw [← coe_substAlgHom hsa, map_zero]
    · show subst a (X j) = a j
      exact subst_X hsa j
  rw [← hfam, ← subst_comp_subst_apply h0X hsa, subst_elim_zero_X F i, subst_X hsa]

end UnitGeneral

section Perturb

variable {τ : Type*} (F : MvFormalGroup g R)

theorem coeff_subst_elim_sub_homogeneous {a y E : Fin g → MvPowerSeries τ R}
    (ha : ∀ j, (a j).constantCoeff = 0) (hy : ∀ j, (y j).constantCoeff = 0)
    {N : ℕ} (hN : 1 ≤ N) (hE : ∀ j, ∀ e : τ →₀ ℕ, coeff e (E j) ≠ 0 → e.degree = N)
    {d : τ →₀ ℕ} (hd : d.degree ≤ N) (i : Fin g) :
    coeff d (subst (Sum.elim a fun j => y j - E j) (F.toPowerSeries i))
      = coeff d (subst (Sum.elim a y) (F.toPowerSeries i)) - coeff d (E i) := by
  classical
  have hE0 : ∀ j, (E j).constantCoeff = 0 := by
    intro j
    by_contra hcon
    have h1 : coeff (0 : τ →₀ ℕ) (E j) ≠ 0 := by
      rwa [coeff_zero_eq_constantCoeff_apply]
    have h2 := hE j 0 h1
    rw [(Finsupp.degree_eq_zero_iff (0 : τ →₀ ℕ)).mpr rfl] at h2
    omega
  have hfam : ∀ s : Fin g ⊕ Fin g,
      ((Sum.elim a fun j => y j - E j) s).constantCoeff = 0 := by
    rintro (j | j)
    · exact ha j
    · show (y j - E j).constantCoeff = 0
      rw [map_sub, hy j, hE0 j, sub_zero]
  have hfam' : ∀ s : Fin g ⊕ Fin g, ((Sum.elim a y) s).constantCoeff = 0 := by
    rintro (j | j)
    exacts [ha j, hy j]

  have key : ∀ m : (Fin g ⊕ Fin g) →₀ ℕ,
      coeff d (m.prod fun s l => (Sum.elim a fun j => y j - E j) s ^ l)
        = coeff d (m.prod fun s l => (Sum.elim a y) s ^ l)
          - ∑ j : Fin g, if m = Finsupp.single (Sum.inr j) 1 then coeff d (E j) else 0 := by
    intro m
    by_cases hm : ∃ j : Fin g, m = Finsupp.single (Sum.inr j) 1
    · obtain ⟨j, rfl⟩ := hm
      rw [Finsupp.prod_single_index
          (h := fun s l => (Sum.elim a fun j' => y j' - E j') s ^ l) (pow_zero _),
        Finsupp.prod_single_index (h := fun s l => (Sum.elim a y) s ^ l) (pow_zero _),
        pow_one, pow_one, Finset.sum_eq_single j
          (fun j' _ hj' => if_neg fun hcon =>
            hj' (Sum.inr_injective (Finsupp.single_left_injective one_ne_zero hcon.symm)))
          (fun hcon => absurd (Finset.mem_univ j) hcon), if_pos rfl]
      show coeff d (y j - E j) = coeff d (y j) - coeff d (E j)
      rw [map_sub]
    · rw [Finset.sum_eq_zero (fun j _ => if_neg fun hcon => hm ⟨j, hcon⟩), sub_zero]
      rcases Nat.lt_or_ge m.degree 2 with hm2 | hm2
      · rcases Nat.lt_or_ge m.degree 1 with hm1 | hm1
        · have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).mp (by omega)
          subst hm0
          rw [Finsupp.prod_zero_index, Finsupp.prod_zero_index]
        · have hmem : m ∈ {d' : (Fin g ⊕ Fin g) →₀ ℕ | d'.degree = 1} := by
            show m.degree = 1
            omega
          rw [← Finsupp.range_single_one] at hmem
          obtain ⟨s, hs⟩ := hmem
          have hs' : Finsupp.single s 1 = m := hs
          rcases s with j | j
          · rw [← hs', Finsupp.prod_single_index
                (h := fun s' l => (Sum.elim a fun j' => y j' - E j') s' ^ l) (pow_zero _),
              Finsupp.prod_single_index (h := fun s' l => (Sum.elim a y) s' ^ l)
                (pow_zero _), pow_one, pow_one]
            rfl
          · exact absurd ⟨j, hs'.symm⟩ hm
      · have hcc : ∀ s : Fin g ⊕ Fin g, ∀ e : τ →₀ ℕ, e.degree < N →
            coeff e ((Sum.elim a fun j => y j - E j) s) = coeff e ((Sum.elim a y) s) := by
          rintro (j | j) e he
          · rfl
          · show coeff e (y j - E j) = coeff e (y j)
            have hEe : coeff e (E j) = 0 := by
              by_contra hcon
              have := hE j e hcon
              omega
            rw [map_sub, hEe, sub_zero]
        exact coeff_finsuppProd_pow_sub_congr hN hfam hfam' hcc (by omega)

  have hsplit : (fun m : (Fin g ⊕ Fin g) →₀ ℕ =>
      coeff m (F.toPowerSeries i)
        • coeff d (m.prod fun s l => (Sum.elim a fun j => y j - E j) s ^ l))
      = fun m =>
        coeff m (F.toPowerSeries i) • coeff d (m.prod fun s l => (Sum.elim a y) s ^ l)
          - coeff m (F.toPowerSeries i)
            • (∑ j : Fin g, if m = Finsupp.single (Sum.inr j) 1 then coeff d (E j) else 0) := by
    funext m
    rw [key m, smul_sub]
  have hfin1 : (Function.support fun m : (Fin g ⊕ Fin g) →₀ ℕ =>
      coeff m (F.toPowerSeries i)
        • coeff d (m.prod fun s l => (Sum.elim a y) s ^ l)).Finite := by
    refine Set.Finite.subset (Finsupp.finite_of_degree_le (σ := Fin g ⊕ Fin g) d.degree) ?_
    intro m hm
    show m.degree ≤ d.degree
    by_contra hcon
    apply hm
    show coeff m (F.toPowerSeries i)
      • coeff d (m.prod fun s l => (Sum.elim a y) s ^ l) = 0
    rw [coeff_finsuppProd_pow_eq_zero_of_degree_lt hfam' (by omega), smul_zero]
  have hfin2 : (Function.support fun m : (Fin g ⊕ Fin g) →₀ ℕ =>
      coeff m (F.toPowerSeries i)
        • (∑ j : Fin g, if m = Finsupp.single (Sum.inr j) 1
            then coeff d (E j) else 0)).Finite := by
    refine Set.Finite.subset
      (Set.finite_range fun j : Fin g => Finsupp.single (Sum.inr j) 1) ?_
    intro m hm
    by_contra hmem
    apply hm
    show coeff m (F.toPowerSeries i)
      • (∑ j : Fin g, if m = Finsupp.single (Sum.inr j) 1 then coeff d (E j) else 0) = 0
    have hz : (∑ j : Fin g, if m = Finsupp.single (Sum.inr j) 1
        then coeff d (E j) else 0) = 0 :=
      Finset.sum_eq_zero fun j _ => if_neg fun hcon => hmem ⟨j, hcon.symm⟩
    rw [hz, smul_zero]
  have hδ : (∑ᶠ m : (Fin g ⊕ Fin g) →₀ ℕ, coeff m (F.toPowerSeries i)
      • (∑ j : Fin g, if m = Finsupp.single (Sum.inr j) 1 then coeff d (E j) else 0))
      = coeff d (E i) := by
    rw [finsum_eq_finsetSum_of_support_subset _
      (s := Finset.univ.image fun j : Fin g => Finsupp.single (Sum.inr j) 1)
      (fun m hm => ?_),
      Finset.sum_image (fun j _ j' _ hjj =>
        Sum.inr_injective (Finsupp.single_left_injective one_ne_zero hjj))]
    · have hterm : ∀ j : Fin g,
          coeff (Finsupp.single (Sum.inr j) 1) (F.toPowerSeries i)
            • (∑ j' : Fin g, if (Finsupp.single (Sum.inr j) 1 : (Fin g ⊕ Fin g) →₀ ℕ)
                = Finsupp.single (Sum.inr j') 1 then coeff d (E j') else 0)
          = (if i = j then 1 else 0) * coeff d (E j) := by
        intro j
        rw [F.coeff_single_inr i j, Finset.sum_eq_single j
          (fun j' _ hj' => if_neg fun hcon =>
            hj' (Sum.inr_injective
              (Finsupp.single_left_injective one_ne_zero hcon)).symm)
          (fun hcon => absurd (Finset.mem_univ j) hcon), if_pos rfl, smul_eq_mul]
      rw [Finset.sum_congr rfl fun j _ => hterm j,
        Finset.sum_eq_single i
          (fun j _ hj => by rw [if_neg fun hcon => hj hcon.symm, zero_mul])
          (fun hcon => absurd (Finset.mem_univ i) hcon), if_pos rfl, one_mul]
    · by_contra hmem
      apply hm
      show coeff m (F.toPowerSeries i)
        • (∑ j : Fin g, if m = Finsupp.single (Sum.inr j) 1 then coeff d (E j) else 0) = 0
      have hz : (∑ j : Fin g, if m = Finsupp.single (Sum.inr j) 1
          then coeff d (E j) else 0) = 0 :=
        Finset.sum_eq_zero fun j _ => if_neg fun hcon => hmem (by
          rw [hcon]
          exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
      rw [hz, smul_zero]
  rw [coeff_subst (hasSubst_of_constantCoeff_zero hfam),
    coeff_subst (hasSubst_of_constantCoeff_zero hfam'), hsplit,
    finsum_sub_distrib hfin1 hfin2, hδ]

end Perturb

section NegSeries

variable {τ : Type*} (F : MvFormalGroup g R)

def negApprox (a : Fin g → MvPowerSeries τ R) : ℕ → Fin g → MvPowerSeries τ R
  | 0 => fun _ => 0
  | n + 1 => fun i =>
      negApprox a n i
        - homogeneousComponent (n + 1)
            (subst (Sum.elim a (negApprox a n)) (F.toPowerSeries i))

@[simp]
theorem negApprox_zero (a : Fin g → MvPowerSeries τ R) :
    negApprox F a 0 = fun _ => 0 := rfl

theorem negApprox_succ (a : Fin g → MvPowerSeries τ R) (n : ℕ) :
    negApprox F a (n + 1) = fun i =>
      negApprox F a n i
        - homogeneousComponent (n + 1)
            (subst (Sum.elim a (negApprox F a n)) (F.toPowerSeries i)) := rfl

theorem constantCoeff_negApprox (a : Fin g → MvPowerSeries τ R) (n : ℕ) (i : Fin g) :
    (negApprox F a n i).constantCoeff = 0 := by
  induction n with
  | zero =>
    show (0 : MvPowerSeries τ R).constantCoeff = 0
    exact map_zero _
  | succ n IH =>
    show (negApprox F a n i - homogeneousComponent (n + 1)
        (subst (Sum.elim a (negApprox F a n)) (F.toPowerSeries i))).constantCoeff = 0
    have h0 : ((0 : τ →₀ ℕ)).degree = 0 :=
      (Finsupp.degree_eq_zero_iff (0 : τ →₀ ℕ)).mpr rfl
    have hne : ((0 : τ →₀ ℕ)).degree ≠ n + 1 := by omega
    rw [map_sub, IH, ← coeff_zero_eq_constantCoeff_apply, coeff_homogeneousComponent,
      if_neg hne, sub_zero]

theorem coeff_subst_elim_negApprox {a : Fin g → MvPowerSeries τ R}
    (ha : ∀ j, (a j).constantCoeff = 0) {n : ℕ} {d : τ →₀ ℕ}
    (hdn : d.degree ≤ n) (hd0 : d ≠ 0) (i : Fin g) :
    coeff d (subst (Sum.elim a (negApprox F a n)) (F.toPowerSeries i)) = 0 := by
  induction n generalizing d with
  | zero =>
    exact absurd ((Finsupp.degree_eq_zero_iff d).mp (Nat.le_zero.mp hdn)) hd0
  | succ n IH =>
    have hy : ∀ j, (negApprox F a n j).constantCoeff = 0 :=
      fun j => constantCoeff_negApprox F a n j
    have hE : ∀ j, ∀ e : τ →₀ ℕ,
        coeff e (homogeneousComponent (n + 1)
          (subst (Sum.elim a (negApprox F a n)) (F.toPowerSeries j))) ≠ 0 →
        e.degree = n + 1 := by
      intro j e hne
      by_contra hcon
      rw [coeff_homogeneousComponent, if_neg hcon] at hne
      exact hne rfl
    rw [negApprox_succ,
      coeff_subst_elim_sub_homogeneous F ha hy (Nat.succ_le_succ (Nat.zero_le n)) hE hdn i]
    rcases Nat.lt_or_ge d.degree (n + 1) with hlt | hge
    · have h1 : coeff d (subst (Sum.elim a (negApprox F a n)) (F.toPowerSeries i)) = 0 :=
        IH (by omega) hd0
      have h2 : coeff d (homogeneousComponent (n + 1)
          (subst (Sum.elim a (negApprox F a n)) (F.toPowerSeries i))) = 0 := by
        rw [coeff_homogeneousComponent, if_neg (by omega)]
      rw [h1, h2, sub_zero]
    · have hdeq : d.degree = n + 1 := by omega
      have h2 : coeff d (homogeneousComponent (n + 1)
          (subst (Sum.elim a (negApprox F a n)) (F.toPowerSeries i)))
          = coeff d (subst (Sum.elim a (negApprox F a n)) (F.toPowerSeries i)) := by
        rw [coeff_homogeneousComponent, if_pos hdeq]
      rw [h2, sub_self]

theorem coeff_negApprox_stable (a : Fin g → MvPowerSeries τ R) {n m : ℕ}
    (hnm : n ≤ m) {d : τ →₀ ℕ} (hd : d.degree ≤ n) (i : Fin g) :
    coeff d (negApprox F a m i) = coeff d (negApprox F a n i) := by
  revert hnm
  induction m with
  | zero =>
    intro hnm
    have hn0 : n = 0 := by omega
    subst hn0
    rfl
  | succ m IH =>
    intro hnm
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · have hstep : coeff d (negApprox F a (m + 1) i) = coeff d (negApprox F a m i) := by
        rw [negApprox_succ]
        show coeff d (negApprox F a m i - homogeneousComponent (m + 1)
            (subst (Sum.elim a (negApprox F a m)) (F.toPowerSeries i)))
          = coeff d (negApprox F a m i)
        rw [map_sub, coeff_homogeneousComponent, if_neg (by omega), sub_zero]
      rw [hstep]
      exact IH (by omega)
    · have hn : n = m + 1 := by omega
      subst hn
      rfl

def negSeries (a : Fin g → MvPowerSeries τ R) : Fin g → MvPowerSeries τ R :=
  fun i => (fun d => coeff d (negApprox F a d.degree i) : (τ →₀ ℕ) → R)

theorem coeff_negSeries (a : Fin g → MvPowerSeries τ R) (d : τ →₀ ℕ) (i : Fin g) :
    coeff d (negSeries F a i) = coeff d (negApprox F a d.degree i) := rfl

theorem coeff_negSeries_eq_negApprox (a : Fin g → MvPowerSeries τ R) {n : ℕ}
    {d : τ →₀ ℕ} (hd : d.degree ≤ n) (i : Fin g) :
    coeff d (negSeries F a i) = coeff d (negApprox F a n i) := by
  rw [coeff_negSeries]
  exact (coeff_negApprox_stable F a hd (le_refl d.degree) i).symm

@[simp]
theorem constantCoeff_negSeries (a : Fin g → MvPowerSeries τ R) (i : Fin g) :
    (negSeries F a i).constantCoeff = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_negSeries,
    (Finsupp.degree_eq_zero_iff (0 : τ →₀ ℕ)).mpr rfl]
  show coeff (0 : τ →₀ ℕ) (0 : MvPowerSeries τ R) = 0
  exact map_zero _

theorem hasSubst_negSeries (a : Fin g → MvPowerSeries τ R) :
    HasSubst (negSeries F a) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_negSeries F a)

theorem subst_elim_negSeries {a : Fin g → MvPowerSeries τ R}
    (ha : ∀ j, (a j).constantCoeff = 0) (i : Fin g) :
    subst (Sum.elim a (negSeries F a)) (F.toPowerSeries i) = 0 := by
  have hneg : ∀ j, (negSeries F a j).constantCoeff = 0 := constantCoeff_negSeries F a
  ext d
  rw [map_zero]
  by_cases hd0 : d = 0
  · subst hd0
    rw [coeff_zero_eq_constantCoeff_apply]
    exact constantCoeff_subst_elim F ha hneg i
  · have hagree : ∀ s : Fin g ⊕ Fin g, ∀ e : τ →₀ ℕ, e.degree ≤ d.degree →
        coeff e ((Sum.elim a (negSeries F a)) s)
          = coeff e ((Sum.elim a (negApprox F a d.degree)) s) := by
      rintro (j | j) e he
      · rfl
      · exact coeff_negSeries_eq_negApprox F a he j
    have hfam1 : ∀ s : Fin g ⊕ Fin g,
        ((Sum.elim a (negSeries F a)) s).constantCoeff = 0 := by
      rintro (j | j)
      exacts [ha j, hneg j]
    have hfam2 : ∀ s : Fin g ⊕ Fin g,
        ((Sum.elim a (negApprox F a d.degree)) s).constantCoeff = 0 := by
      rintro (j | j)
      exacts [ha j, constantCoeff_negApprox F a _ j]
    rw [coeff_subst_congr hfam1 hfam2 hagree (F.toPowerSeries i) (le_refl d.degree)]
    exact coeff_subst_elim_negApprox F ha (le_refl d.degree) hd0 i

theorem coeff_single_negSeries {a : Fin g → MvPowerSeries τ R}
    (ha : ∀ j, (a j).constantCoeff = 0) (t : τ) (i : Fin g) :
    coeff (Finsupp.single t 1) (negSeries F a i)
      = - coeff (Finsupp.single t 1) (a i) := by
  have hdeg : (Finsupp.single t 1).degree = 1 := Finsupp.degree_single t 1
  rw [coeff_negSeries, hdeg]
  show coeff (Finsupp.single t 1) (negApprox F a (0 + 1) i)
    = - coeff (Finsupp.single t 1) (a i)
  rw [negApprox_succ]
  show coeff (Finsupp.single t 1) (negApprox F a 0 i - homogeneousComponent (0 + 1)
      (subst (Sum.elim a (negApprox F a 0)) (F.toPowerSeries i)))
    = - coeff (Finsupp.single t 1) (a i)
  simp only [negApprox_zero]
  rw [map_sub, map_zero, zero_sub, coeff_homogeneousComponent, if_pos (by omega),
    subst_elim_zero_right F ha i]

end NegSeries

section Group

variable {τ τ' : Type*} (F : MvFormalGroup g R)

theorem subst_subst_elim {u v : Fin g → MvPowerSeries τ R}
    (hu : ∀ j, (u j).constantCoeff = 0) (hv : ∀ j, (v j).constantCoeff = 0)
    {b : τ → MvPowerSeries τ' R} (hb : HasSubst b) (i : Fin g) :
    subst b (subst (Sum.elim u v) (F.toPowerSeries i))
      = subst (Sum.elim (fun j => subst b (u j)) fun j => subst b (v j))
        (F.toPowerSeries i) := by
  rw [subst_comp_subst_apply (hasSubst_elim hu hv) hb]
  congr 1
  funext s
  rcases s with j | j <;> rfl

theorem subst_elim_negSeries_left {a : Fin g → MvPowerSeries τ R}
    (ha : ∀ j, (a j).constantCoeff = 0) (i : Fin g) :
    subst (Sum.elim (negSeries F a) a) (F.toPowerSeries i) = 0 := by
  have hy : ∀ j, (negSeries F a j).constantCoeff = 0 := constantCoeff_negSeries F a
  have hz : ∀ j, (negSeries F (negSeries F a) j).constantCoeff = 0 :=
    constantCoeff_negSeries F _
  have tup1 : ∀ j, subst (Sum.elim (negSeries F a) (negSeries F (negSeries F a)))
      (F.toPowerSeries j) = 0 := subst_elim_negSeries F hy
  have haz : a = negSeries F (negSeries F a) := by
    funext j
    have s1 : a j = subst (Sum.elim a fun _ => 0) (F.toPowerSeries j) :=
      (subst_elim_zero_right F ha j).symm
    have s2 : (fun _ : Fin g => (0 : MvPowerSeries τ R))
        = fun j' => subst (Sum.elim (negSeries F a) (negSeries F (negSeries F a)))
            (F.toPowerSeries j') := by
      funext j'
      exact (tup1 j').symm
    have s3 : subst (Sum.elim a fun j' => subst (Sum.elim (negSeries F a)
          (negSeries F (negSeries F a))) (F.toPowerSeries j')) (F.toPowerSeries j)
        = subst (Sum.elim (fun j' => subst (Sum.elim a (negSeries F a))
            (F.toPowerSeries j')) (negSeries F (negSeries F a))) (F.toPowerSeries j) :=
      (subst_elim_assoc F ha hy hz j).symm
    have s4 : (fun j' => subst (Sum.elim a (negSeries F a)) (F.toPowerSeries j'))
        = fun _ : Fin g => (0 : MvPowerSeries τ R) := by
      funext j'
      exact subst_elim_negSeries F ha j'
    rw [s1, s2, s3, s4, subst_elim_zero_left F hz j]
  nth_rewrite 2 [haz]
  exact tup1 i

theorem negSeries_unique {a y : Fin g → MvPowerSeries τ R}
    (ha : ∀ j, (a j).constantCoeff = 0) (hy : ∀ j, (y j).constantCoeff = 0)
    (h : ∀ i, subst (Sum.elim a y) (F.toPowerSeries i) = 0) :
    y = negSeries F a := by
  have hneg : ∀ j, (negSeries F a j).constantCoeff = 0 := constantCoeff_negSeries F a
  funext j
  have s1 : y j = subst (Sum.elim (fun _ => 0) y) (F.toPowerSeries j) :=
    (subst_elim_zero_left F hy j).symm
  have s2 : (fun _ : Fin g => (0 : MvPowerSeries τ R))
      = fun j' => subst (Sum.elim (negSeries F a) a) (F.toPowerSeries j') := by
    funext j'
    exact (subst_elim_negSeries_left F ha j').symm
  have s3 : subst (Sum.elim (fun j' => subst (Sum.elim (negSeries F a) a)
        (F.toPowerSeries j')) y) (F.toPowerSeries j)
      = subst (Sum.elim (negSeries F a) fun j' => subst (Sum.elim a y)
          (F.toPowerSeries j')) (F.toPowerSeries j) :=
    subst_elim_assoc F hneg ha hy j
  have s4 : (fun j' => subst (Sum.elim a y) (F.toPowerSeries j'))
      = fun _ : Fin g => (0 : MvPowerSeries τ R) := by
    funext j'
    exact h j'
  rw [s1, s2, s3, s4, subst_elim_zero_right F hneg j]

theorem negSeries_unique_left {a y : Fin g → MvPowerSeries τ R}
    (ha : ∀ j, (a j).constantCoeff = 0) (hy : ∀ j, (y j).constantCoeff = 0)
    (h : ∀ i, subst (Sum.elim y a) (F.toPowerSeries i) = 0) :
    y = negSeries F a := by

  have hneg : ∀ j, (negSeries F a j).constantCoeff = 0 := constantCoeff_negSeries F a
  funext j
  have s1 : y j = subst (Sum.elim y fun _ => 0) (F.toPowerSeries j) :=
    (subst_elim_zero_right F hy j).symm
  have s2 : (fun _ : Fin g => (0 : MvPowerSeries τ R))
      = fun j' => subst (Sum.elim a (negSeries F a)) (F.toPowerSeries j') := by
    funext j'
    exact (subst_elim_negSeries F ha j').symm
  have s3 : subst (Sum.elim y fun j' => subst (Sum.elim a (negSeries F a))
        (F.toPowerSeries j')) (F.toPowerSeries j)
      = subst (Sum.elim (fun j' => subst (Sum.elim y a) (F.toPowerSeries j'))
          (negSeries F a)) (F.toPowerSeries j) :=
    (subst_elim_assoc F hy ha hneg j).symm
  have s4 : (fun j' => subst (Sum.elim y a) (F.toPowerSeries j'))
      = fun _ : Fin g => (0 : MvPowerSeries τ R) := by
    funext j'
    exact h j'
  rw [s1, s2, s3, s4, subst_elim_zero_left F hneg j]

end Group

section InvSeries

variable (F : MvFormalGroup g R)

def invSeries : Fin g → MvPowerSeries (Fin g) R :=
  negSeries F fun j => X j

@[simp]
theorem constantCoeff_invSeries (i : Fin g) : (invSeries F i).constantCoeff = 0 :=
  constantCoeff_negSeries F _ i

theorem hasSubst_invSeries : HasSubst (invSeries F) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_invSeries F)

theorem subst_elim_X_invSeries (i : Fin g) :
    subst (Sum.elim (fun j => (X j : MvPowerSeries (Fin g) R)) (invSeries F))
      (F.toPowerSeries i) = 0 :=
  subst_elim_negSeries F (fun j => constantCoeff_X j) i

theorem subst_elim_invSeries_X (i : Fin g) :
    subst (Sum.elim (invSeries F) fun j => (X j : MvPowerSeries (Fin g) R))
      (F.toPowerSeries i) = 0 :=
  subst_elim_negSeries_left F (fun j => constantCoeff_X j) i

end InvSeries

section NegSeriesMore

variable {τ τ' : Type*} (F : MvFormalGroup g R)

theorem subst_negSeries [Finite τ] {a : Fin g → MvPowerSeries τ R}
    (ha : ∀ j, (a j).constantCoeff = 0) {b : τ → MvPowerSeries τ' R}
    (hb0 : ∀ s, (b s).constantCoeff = 0) :
    (fun i => subst b (negSeries F a i)) = negSeries F fun i => subst b (a i) := by
  have hb : HasSubst b := hasSubst_of_constantCoeff_zero hb0
  have hneg : ∀ j, (negSeries F a j).constantCoeff = 0 := constantCoeff_negSeries F a
  refine negSeries_unique F (fun j => constantCoeff_subst_eq_zero hb hb0 (ha j))
    (fun j => constantCoeff_subst_eq_zero hb hb0 (hneg j)) fun i => ?_
  rw [← subst_subst_elim F ha hneg hb i, subst_elim_negSeries F ha i,
    ← coe_substAlgHom hb, map_zero]

theorem negSeries_elim_add [IsComm F] {a b : Fin g → MvPowerSeries τ R}
    (ha : ∀ j, (a j).constantCoeff = 0) (hb : ∀ j, (b j).constantCoeff = 0) :
    negSeries F (fun i => subst (Sum.elim a b) (F.toPowerSeries i))
      = fun i => subst (Sum.elim (negSeries F a) (negSeries F b))
          (F.toPowerSeries i) := by
  have hna : ∀ j, (negSeries F a j).constantCoeff = 0 := constantCoeff_negSeries F a
  have hnb : ∀ j, (negSeries F b j).constantCoeff = 0 := constantCoeff_negSeries F b
  refine (negSeries_unique F (fun j => constantCoeff_subst_elim F ha hb j)
    (fun j => constantCoeff_subst_elim F hna hnb j) fun i => ?_).symm
  rw [subst_elim_exchange F ha hb hna hnb i]
  have hzl : (fun j => subst (Sum.elim a (negSeries F a)) (F.toPowerSeries j))
      = fun _ : Fin g => (0 : MvPowerSeries τ R) := by
    funext j
    exact subst_elim_negSeries F ha j
  have hzr : (fun j => subst (Sum.elim b (negSeries F b)) (F.toPowerSeries j))
      = fun _ : Fin g => (0 : MvPowerSeries τ R) := by
    funext j
    exact subst_elim_negSeries F hb j
  rw [hzl, hzr]
  exact subst_elim_zero_right F (fun _ => map_zero _) i

end NegSeriesMore

namespace Hom

variable {F : MvFormalGroup g R} {G : MvFormalGroup h R}

def neg [IsComm G] (φ : Hom F G) : Hom F G where
  toPowerSeries := negSeries G φ.toPowerSeries
  constantCoeff_eq_zero := constantCoeff_negSeries G φ.toPowerSeries
  subst_eq := by
    intro i
    have hφ : ∀ j, (φ.toPowerSeries j).constantCoeff = 0 := φ.constantCoeff_eq_zero
    have hbF : ∀ s, ((F.toPowerSeries) s).constantCoeff = 0 := F.constantCoeff_eq_zero
    have hXl0 : ∀ l : Fin g,
        ((X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)).constantCoeff = 0 :=
      fun l => constantCoeff_X _
    have hXr0 : ∀ l : Fin g,
        ((X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)).constantCoeff = 0 :=
      fun l => constantCoeff_X _
    have hφL : ∀ j, (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
        (φ.toPowerSeries j)).constantCoeff = 0 :=
      fun j => constantCoeff_subst_eq_zero
        (hasSubst_of_constantCoeff_zero hXl0) hXl0 (hφ j)
    have hφR : ∀ j, (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
        (φ.toPowerSeries j)).constantCoeff = 0 :=
      fun j => constantCoeff_subst_eq_zero
        (hasSubst_of_constantCoeff_zero hXr0) hXr0 (hφ j)
    calc subst F.toPowerSeries (negSeries G φ.toPowerSeries i)
        = negSeries G (fun j => subst F.toPowerSeries (φ.toPowerSeries j)) i :=
          congrFun (subst_negSeries G hφ hbF) i
      _ = negSeries G (fun j => subst (Sum.elim
            (fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j'))
            fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j')) (G.toPowerSeries j)) i := by
          have hc : (fun j => subst F.toPowerSeries (φ.toPowerSeries j))
              = fun j => subst (Sum.elim
                (fun j' => subst
                  (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
                  (φ.toPowerSeries j'))
                fun j' => subst
                  (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
                  (φ.toPowerSeries j')) (G.toPowerSeries j) := by
            funext j
            exact φ.subst_eq j
          rw [hc]
      _ = subst (Sum.elim
            (negSeries G fun j' => subst
              (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j'))
            (negSeries G fun j' => subst
              (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j'))) (G.toPowerSeries i) :=
          congrFun (negSeries_elim_add G hφL hφR) i
      _ = subst (Sum.elim
            (fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (negSeries G φ.toPowerSeries j'))
            fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (negSeries G φ.toPowerSeries j') ) (G.toPowerSeries i) := by
          rw [← subst_negSeries G hφ hXl0, ← subst_negSeries G hφ hXr0]

@[simp]
theorem toPowerSeries_neg [IsComm G] (φ : Hom F G) :
    (Hom.neg φ).toPowerSeries = negSeries G φ.toPowerSeries := rfl

instance instNeg [IsComm G] : Neg (Hom F G) := ⟨Hom.neg⟩

instance instAddCommGroup [IsComm G] : AddCommGroup (Hom F G) :=
  { Hom.instAddCommMonoid with
    neg := Hom.neg
    zsmul := zsmulRec
    neg_add_cancel := fun φ => by
      apply Hom.ext
      funext i
      show subst (Sum.elim (negSeries G φ.toPowerSeries) φ.toPowerSeries)
          (G.toPowerSeries i) = 0
      exact subst_elim_negSeries_left G φ.constantCoeff_eq_zero i }

@[simp]
theorem toPowerSeries_neg' [IsComm G] (φ : Hom F G) :
    (-φ).toPowerSeries = negSeries G φ.toPowerSeries := rfl

@[simp]
theorem toPowerSeries_sub [IsComm G] (φ ψ : Hom F G) :
    (φ - ψ).toPowerSeries = fun i =>
      subst (Sum.elim φ.toPowerSeries (negSeries G ψ.toPowerSeries))
        (G.toPowerSeries i) := rfl

end Hom

namespace End

variable (F : MvFormalGroup g R)

instance instAddCommGroup [IsComm F] : AddCommGroup (End F) :=
  inferInstanceAs (AddCommGroup (Hom F F))

instance instRing [IsComm F] : Ring (End F) :=
  { End.instSemiring F, End.instAddCommGroup F with }

@[simp]
theorem toPowerSeries_neg [IsComm F] (φ : End F) :
    Hom.toPowerSeries (-φ) = negSeries F (Hom.toPowerSeries φ) := rfl

@[simp]
theorem toPowerSeries_sub [IsComm F] (φ ψ : End F) :
    Hom.toPowerSeries (φ - ψ) = fun i =>
      subst (Sum.elim (Hom.toPowerSeries φ) (negSeries F (Hom.toPowerSeries ψ)))
        (F.toPowerSeries i) := rfl

theorem toPowerSeries_neg_one [IsComm F] :
    Hom.toPowerSeries (-1 : End F) = invSeries F := by
  rw [toPowerSeries_neg]
  show negSeries F (Hom.toPowerSeries (1 : End F)) = invSeries F
  rw [toPowerSeries_one]
  rfl

theorem toPowerSeries_intCast_ofNat [IsComm F] (n : ℕ) :
    Hom.toPowerSeries (((n : ℕ) : ℤ) : End F) = F.nthSeries n := by
  rw [Int.cast_natCast]
  exact toPowerSeries_natCast F n

theorem toPowerSeries_intCast_negSucc [IsComm F] (n : ℕ) :
    Hom.toPowerSeries ((Int.negSucc n : ℤ) : End F)
      = negSeries F (F.nthSeries (n + 1)) := by
  rw [Int.cast_negSucc, toPowerSeries_neg]
  show negSeries F (Hom.toPowerSeries (((n + 1 : ℕ) : End F))) = _
  rw [toPowerSeries_natCast]

end End

section InvHom

variable (F : MvFormalGroup g R)

def invHom [IsComm F] : End F := -(1 : End F)

@[simp]
theorem toPowerSeries_invHom [IsComm F] :
    Hom.toPowerSeries (invHom F) = invSeries F :=
  End.toPowerSeries_neg_one F

end InvHom

section LinearPartNeg

variable (F : MvFormalGroup g R)

theorem linearPart_negSeries {k : ℕ} {a : Fin g → MvPowerSeries (Fin k) R}
    (ha : ∀ j, (a j).constantCoeff = 0) :
    linearPart (negSeries F a) = - linearPart a := by
  ext i j
  show coeff (Finsupp.single j 1) (negSeries F a i)
    = (- linearPart a) i j
  rw [coeff_single_negSeries F ha j i, Matrix.neg_apply]
  rfl

theorem coeff_single_invSeries (t i : Fin g) :
    coeff (Finsupp.single t 1) (invSeries F i)
      = - coeff (Finsupp.single t 1) (X i : MvPowerSeries (Fin g) R) :=
  coeff_single_negSeries F (fun l => constantCoeff_X l) t i

theorem linearPart_invSeries : linearPart (invSeries F) = -1 := by
  classical
  ext i j
  show coeff (Finsupp.single j 1) (invSeries F i)
    = (-1 : Matrix (Fin g) (Fin g) R) i j
  rw [coeff_single_invSeries F j i, coeff_index_single_X, Matrix.neg_apply,
    Matrix.one_apply]
  by_cases hij : j = i
  · subst hij
    rfl
  · rw [if_neg hij, if_neg fun hcon => hij hcon.symm, neg_zero]

@[simp]
theorem linearPartHom_neg [IsComm F] (φ : End F) :
    linearPartHom F (-φ) = - linearPartHom F φ :=
  map_neg (linearPartHom F) φ

theorem linearPartHom_neg_one [IsComm F] :
    linearPartHom F (-1 : End F) = -1 := by
  rw [map_neg, map_one]

@[simp]
theorem linearPartHom_intCast [IsComm F] (n : ℤ) :
    linearPartHom F ((n : ℤ) : End F) = n • (1 : Matrix (Fin g) (Fin g) R) := by
  rw [map_intCast, zsmul_eq_mul, mul_one]

end LinearPartNeg

end MvFormalGroup


