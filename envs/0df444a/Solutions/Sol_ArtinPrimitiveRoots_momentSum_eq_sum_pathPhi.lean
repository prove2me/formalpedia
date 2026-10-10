-- Prove2me | solution 1 for ArtinPrimitiveRoots.momentSum_eq_sum_pathPhi
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T01:23:53.134261+00:00
-- url     : https://prove2.me/submissions/f343d084-a7b4-4661-9d61-ae1cdcd1487d

import Mathlib
import Definitions.Def_ArtinMinorOperator
import Definitions.Def_ArtinSieve
import Definitions.Def_ArtinMarkedSquare
import Definitions.Def_ArtinMinorSquare
import Definitions.Def_ArtinMemoryModel

section
/-! # L102D_OpDefs — alias of the bundle `Def_ArtinMinorOperator` (round 5)

The operator model now lives in `Definitions/Def_ArtinMinorOperator.lean` (same declarations, same
names). This module re-exports it and keeps `listProd`, which only the proofs use. -/

namespace ArtinPrimitiveRoots

/-- The product of all labels of a list. -/
def listProd {K J : ℕ} (ℓ : Fin K → Fin (J + 1) → ℕ) : ℕ := ∏ i, ∏ j, ℓ i j

end ArtinPrimitiveRoots
end

section
/-! # L102D: the spectral Hölder step of [21] §3.3, (3.20), in abstract form

For a finite-dimensional complex inner product space `E`, an operator `A` and `B = A A†`:

* `re_inner_pow_eq_sum`: `re ⟪v, Tᵏ v⟫ = ∑ λᵢᵏ ‖cᵢ‖²` in an eigenbasis of a symmetric `T`;
* `re_inner_le_pow` (spectral Hölder): `re ⟪f, B f⟫ ≤ ‖f‖^{2(1-1/R)} (re ⟪f, Bᴿ f⟫)^{1/R}`
  for a positive symmetric `B`;
* `norm_inner_apply_le_moment`: `‖⟪f, A g⟫‖ ≤ ‖g‖ ‖f‖^{1-1/R} (re ⟪f, (A A†)ᴿ f⟫)^{1/(2R)}`;
* `re_inner_sum_le_trace` (largest eigenvalue ≤ trace): for `f = ∑ cₚ uₚ` and a positive `C`,
  `re ⟪f, C f⟫ ≤ (∑ |cₚ|²) (∑ re ⟪uₚ, C uₚ⟫)`;
* `norm_sum_inner_le_moment` (the localized Hölder step): for blocks `j`,
  `‖∑ⱼ ⟪fⱼ, A gⱼ⟫‖ ≤ (∑ ‖gⱼ‖²)^{1/2} (∑ ‖fⱼ‖²)^{(1-1/R)/2} (∑ⱼ re ⟪fⱼ, (A A†)ᴿ fⱼ⟫)^{1/(2R)}`.

These are exactly the inequalities used between (3.19) and (3.20) of [21]; the concrete inputs
(the slope-interval partition with `O(H)` primitive positions per interval, and the norm bounds
(3.18)) are separate. -/

namespace ArtinPrimitiveRoots.L102D

open RCLike Finset
open scoped InnerProductSpace ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the localized spectral Hölder step of (3.20) for matrices

For a matrix `A` on a finite index set of states with positions `pos : ι → P`, a vector `f`
constant on positions, and a block index `blk : P → ℤ` such that `A` only connects blocks at
distance `≤ W` and each block has `≤ κ` positions,
`|⟨f, A f⟩| ≤ ((2W+1)‖f‖²)^{1/2} (‖f‖²)^{(1-1/R)/2} (κ F² M)^{1/(2R)}`,
`M = ∑_P ⟨u_P, (AA*)^R u_P⟩`, `F = sup |f|`. -/

namespace ArtinPrimitiveRoots.L102D

open Finset Matrix WithLp
open scoped InnerProductSpace ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end ArtinPrimitiveRoots.L102D
end

section
/-!
# Elementary divisor-sum estimates
-/

namespace ArtinBV

open Finset

end ArtinBV
end

section
/-! # L102D: the exact outer reduction of (10.9) ([21] §3.1, (3.10)–(3.11))

`Q_Y − Q_Y^maj = Q^sh − Q^{maj,sh} + Q^min`, where `Q^sh`, `Q^{maj,sh}` are the parts of the two
squares over label pairs whose products `a, b` are not coprime, and `Q^min` is the coprime part
of the minor-arc square, with kernel `ψ(t/Y) ∫_{[0,1) ∖ 𝔐} e(θ(t − b + a)) dθ`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

/-! ## Elementary inputs -/

/-! ## The identity -/

/-! ## The reduction of (10.9) to the shared-label bound (D1b) and the minor-arc bound (D1c) -/

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: good positions and their measure ([21] §3.2, Lemma 3.2)

For lists `ℓ` of `M` primes in each group, the omission products `D` (omit one label per group),
the two good-state tests on a ratio `r ∈ ℝ/ℤ` (realized on `(0, 1]`), and Lemma 3.2: the set of
`r` failing goodness has measure at most `exp(-c L^{0.1})`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

/-! ## Distance to the nearest integer and its level sets -/

/-! ## Test (i): the union bound -/

/-! ## Markov's inequality for a finite weighted family of bad sets -/

/-! ## Test (ii): one fresh draw, then Markov over the fresh draws -/

/-! ## Counting and asymptotics -/

/-! ## Lemma 3.2 -/

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the divisor input (3.9) of [21] §3.1

`∑_{h ≤ Z} τ(1 + l h)² ≤ 4 (Z + T)(1 + log T)³` whenever every `m` with `m⁴ ≤ (1 + lZ)³` is
`≤ T`. The proof replaces `τ(n)² = #{(d₁, d₂) : d₁, d₂ ∣ n}` by four times the number of divisor
pairs with `lcm⁴ ≤ n³` (one of `(d₁,d₂)`, `(n/d₁,n/d₂)`, `(d₁,n/d₂)`, `(n/d₁,d₂)` qualifies), and
then counts `h` in one residue class modulo the `lcm`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the shared-label parts are negligible ([21] §3.1 (3.9), §4.9 (4.61), (4.63))

Bounds for the inner sums `rawInner`, `majInner` at one pair of label products, for the measure of
the major arcs, and for the normalized mass of label pairs with a common prime. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

/-! ## Elementary facts about the cutoffs and coefficients -/

/-! ## The measure of the major arcs -/

/-! ## The raw inner sum at one pair of label products -/

/-! ## The major inner sum at one pair of label products -/

/-! ## The mass of label pairs with a common prime -/

/-! ## Inputs about the groups for large `x` -/

/-! ## Numerics -/


/-! ## D1b: the shared-label bound -/

/-- Common setting: the hypotheses used by both halves of D1b, at one `x`. -/
structure SharedSetting (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (Y Hm Hn : ℝ) (α β : ℕ → ℂ) (C : ℝ) :
    Prop where
  hL1 : 1 ≤ log x
  hx : 0 < x
  hHm : 0 < Hm
  hHn : 0 < Hn
  hY : 1 ≤ Y
  hX1 : 1 ≤ Hm * Hn
  hα0 : α 0 = 0
  hβ0 : β 0 = 0
  hαb : ∀ m, ‖α m‖ ≤ log x ^ C
  hβb : ∀ n, ‖β n‖ ≤ log x ^ C
  hV : ∀ j, (1 : ℝ) / 2 ≤ groupReciprocalSum x (a j)
  hab : ∀ i, (0.1 : ℝ) < a i
  hlog : 1 + log (17 * (Hm * Hn)) ≤ 2 * log x


end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the cuts of D1c (`minor_square_bound`) and the reduction

Four statements about the operator model of `L102D_OpDefs` (draft bundle
`Def_ArtinMinorOperator`):

* `MomentBoundStmt` (D7, [21] (3.19)/(4.1)): the moment of `(AA*)^R` is `≤ UV L^{-E₀ N}`;
* `PairingFromMomentStmt` (D5, [21] (3.20)): the pairing `⟨f, A f⟩_σ` is controlled by the moment;
* `GoodnessRemovalStmt` (D8a, [21] (4.56)–(4.57)): removing `G` from the pairing costs `UV L^{-A}`;
* `PadLiftStmt` (D8bc, [21] (4.58)–(4.63)): `Q^min = ∑_{dyads} d₀⁻¹ ⟨f, S T S f⟩_σ + O(XY L^{-A})`.

`minor_square_bound_of_cuts` proves the D1c statement from the four. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: D5, the pairing from the moment ([21] §3.3, (3.20)), for the operator model

The concrete inputs to `norm_qform_le_blocks`: `A` only connects slope blocks at distance `≤ 12`,
a slope block of length `H/U²` holds `≤ 17(512H + 1)` primitive positions, `f` depends only on the
position, `|f| ≤ L^{2C}`, and `σ ∑ |f|² ≤ 32 U V L^{4C}` ((3.18)). -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

section Geometry

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {J : ℕ} {U V : ℝ}

lemma mem_posBox_of_state (s : PhysState x a J U V) : s.1.1 ∈ posBox U V :=
  (mem_product.1 (mem_filter.1 s.2).1).1

lemma state_pos_bounds (hU : 0 < U) (hV : 0 < V) (s : PhysState x a J U V) :
    U ≤ s.1.1.1 ∧ (s.1.1.1 : ℝ) ≤ 16 * U ∧ Nat.Coprime s.1.1.1 s.1.1.2 ∧
      V ≤ s.1.1.2 ∧ (s.1.1.2 : ℝ) ≤ 2 * V := by
  have h := mem_posBox_of_state s
  simp only [posBox, mem_filter, mem_product, mem_Icc] at h
  obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ := h
  exact ⟨(Nat.le_ceil U).trans (by exact_mod_cast h1),
    (Nat.cast_le.2 h2).trans (Nat.floor_le (by linarith)), h5,
    (Nat.le_ceil V).trans (by exact_mod_cast h3), (Nat.cast_le.2 h4).trans (Nat.floor_le (by linarith))⟩

end Geometry

/-! ## Slope blocks -/

/-! ## The endpoint norm (3.18) -/

section Norm

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ}

/-- Disjoint groups: entries of a list of a state are pairwise distinct primes, so their product
divides `P₁`. -/
lemma listProd_dvd_of_disjoint {J : ℕ} {U V : ℝ}
    (hdisj : ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)))
    (s : PhysState x a J U V) : listProd s.1.2 ∣ s.1.1.1 := by
  have hs := mem_filter.1 s.2
  obtain ⟨hmem, hinj, hdvd⟩ := hs
  have hcand := (mem_product.1 hmem).2
  have hgrp : ∀ i j, s.1.2 i j ∈ primeGroup x (a i) := fun i j =>
    Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hcand i) j
  have hprime : ∀ i j, (s.1.2 i j).Prime := fun i j => by
    have := hgrp i j; unfold primeGroup at this; exact (mem_filter.1 this).2.1
  have hne : ∀ q q' : Fin K × Fin (J + 1), q ≠ q' → s.1.2 q.1 q.2 ≠ s.1.2 q'.1 q'.2 := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hq heq
    by_cases hi : i = i'
    · subst hi
      have : j = j' := hinj i heq
      exact hq (by rw [this])
    · exact Finset.disjoint_left.1 (hdisj i i' hi) (hgrp i j) (heq ▸ hgrp i' j')
  have hZ : (∏ q : Fin K × Fin (J + 1), ((s.1.2 q.1 q.2 : ℕ) : ℤ)) ∣ (s.1.1.1 : ℤ) := by
    refine Fintype.prod_dvd_of_coprime (fun q q' hqq => ?_) fun q => ?_
    · simp only [Function.onFun]
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
      exact (Nat.coprime_primes (hprime q.1 q.2) (hprime q'.1 q'.2)).2 (hne q q' hqq)
    · exact_mod_cast hdvd q.1 q.2
  have : ((listProd s.1.2 : ℕ) : ℤ) ∣ (s.1.1.1 : ℤ) := by
    unfold listProd; push_cast
    have e := Fintype.prod_prod_type' (fun (i : Fin K) (j : Fin (J + 1)) => ((s.1.2 i j : ℕ) : ℤ))
    rw [e] at hZ
    exact hZ
  exact_mod_cast this

end Norm


/-! ## D5 at one `x` -/


/-! ## Large-`x` inputs and D5 -/

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: D8bc, the pad lift ([21] §4.9, (4.58)–(4.63))

The dyadic sum of the unprojected pairings `2^{-k} ⟨f, S T S f⟩_σ` reproduces `Q^min` up to the pad
configurations that collide. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

section GroupPart

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ}

end GroupPart

/-! ## Lists of a state -/

section Lists

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {J : ℕ}

/-- The structural hypotheses on a list: entries in their groups, injective in each group,
groups pairwise disjoint. -/
structure ListOK (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (J : ℕ) (ℓ : Fin K → Fin (J + 1) → ℕ) : Prop where
  grp : ∀ i j, ℓ i j ∈ primeGroup x (a i)
  inj : ∀ i, Function.Injective (ℓ i)
  disj : ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j))

/-- The set of entries of a list. -/
def entries (ℓ : Fin K → Fin (J + 1) → ℕ) : Finset ℕ :=
  univ.image fun q : Fin K × Fin (J + 1) => ℓ q.1 q.2

end Lists

/-! ## The endpoint vector at a constructed position -/

section Endpoint

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {J : ℕ}

end Endpoint

/-! ## Step A: `⟨f, S T S f⟩ = ⟨f, T f⟩` -/

section SlotSym

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {J : ℕ} {U V : ℝ}

/-- The orbit relation of the slot permutations. -/
def orbRel (s t : PhysState x a J U V) : Prop :=
  t.1.1 = s.1.1 ∧ ∀ i, Set.range (t.1.2 i) = Set.range (s.1.2 i)

lemma orbRel_symm {s t : PhysState x a J U V} (h : orbRel s t) : orbRel t s :=
  ⟨h.1.symm, fun i => (h.2 i).symm⟩

lemma orbRel_trans {s t u : PhysState x a J U V} (h1 : orbRel s t) (h2 : orbRel t u) :
    orbRel s u :=
  ⟨h2.1.trans h1.1, fun i => (h2.2 i).trans (h1.2 i)⟩

open Classical in
lemma slotSym_apply (s s' : PhysState x a J U V) :
    slotSym x a J U V s s' = if orbRel s s' then
      ((univ.filter fun t => orbRel s t).card : ℂ)⁻¹ else 0 := by
  unfold slotSym orbRel
  by_cases h : s'.1.1 = s.1.1 ∧ ∀ i, Set.range (s'.1.2 i) = Set.range (s.1.2 i)
  · rw [if_pos ⟨h.1.symm, h.2⟩, if_pos h]; congr 2; convert rfl
  · rw [if_neg (fun h' => h ⟨h'.1.symm, h'.2⟩), if_neg h]

open Classical in
lemma orbit_card_eq {s s' : PhysState x a J U V} (h : orbRel s s') :
    (univ.filter fun t => orbRel s t).card = (univ.filter fun t => orbRel s' t).card := by
  congr 1; ext t; simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun ht => orbRel_trans (orbRel_symm h) ht, fun ht => orbRel_trans h ht⟩

end SlotSym

/-! ## Step B: configurations and state pairs -/

section Configs

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {J : ℕ}

end Configs

/-! ## The value identity -/

section Value

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {J : ℕ}

end Value

/-! ## The bijection -/

section Bijection

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {J : ℕ}

end Bijection

section Bijection2

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {J : ℕ}

end Bijection2

/-! ## Steps C and D -/

section StepsCD

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {J : ℕ}

end StepsCD

/-! ## The difference identity -/

section Difference

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {J : ℕ}

end Difference

/-! ## Step E: the collision mass -/

section Collision

variable {J : ℕ}

end Collision

section Collision2

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {J : ℕ}

end Collision2

/-! ## Step E: the bound at one `x` -/

section StepE

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ}

end StepE

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D_MemDefs — alias of the bundle `Def_ArtinMemoryModel` (round 5)

The memory model (root coordinates, `pathPhi`, `rootIL`, the memory space, `ghostOp`, `edgeOp`,
`memMomentD`, `dyadParams`, and `MemParams.RootIn`) now lives in
`Definitions/Def_ArtinMemoryModel.lean` (same declarations, same names). -/
end

section
/-! # L102D: root coordinates of a primitive position (for D7p)

For a primitive `P₀ = (u, v)` with `u ≥ 1`: `c = (−v⁻¹ mod u)`, `d = (1 + vc)/u`, the completion
`g = (u c; v d) ∈ SL₂(ℤ)`, `g z = (u z₁ + c z₂, v z₁ + d z₂)` and its inverse. Box conditions,
divisibility, goodness and the damping count transfer between `P = g z` and `z`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

/-- `c = (−v⁻¹ mod u)`. -/
noncomputable def rc (u v : ℕ) : ℤ := ((-(v : ZMod u)⁻¹ : ZMod u).val : ℤ)

/-- `d = (1 + v c)/u`. -/
noncomputable def rd (u v : ℕ) : ℤ := (1 + v * rc u v) / u

lemma dvd_one_add_rc {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) :
    (u : ℤ) ∣ 1 + v * rc u v := by
  have : NeZero u := ⟨hu.ne'⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [rc]
  push_cast
  rw [ZMod.natCast_zmod_val, mul_neg, ZMod.coe_mul_inv_eq_one v hcop.symm]
  ring

lemma u_mul_rd {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) :
    (u : ℤ) * rd u v = 1 + v * rc u v := by
  unfold rd; exact Int.mul_ediv_cancel' (dvd_one_add_rc hu hcop)

lemma rdet {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) :
    (u : ℤ) * rd u v - rc u v * v = 1 := by
  rw [u_mul_rd hu hcop]; ring

lemma rc_nonneg (u v : ℕ) : 0 ≤ rc u v := by unfold rc; positivity

lemma rc_lt {u v : ℕ} (hu : 0 < u) : rc u v < u := by
  have : NeZero u := ⟨hu.ne'⟩
  unfold rc; exact_mod_cast ZMod.val_lt _

/-- `g z`. -/
noncomputable def gz (u v : ℕ) (z : ℤ × ℤ) : ℤ × ℤ :=
  ((u : ℤ) * z.1 + rc u v * z.2, (v : ℤ) * z.1 + rd u v * z.2)

/-- `g⁻¹ P`. -/
noncomputable def ginv (u v : ℕ) (P : ℤ × ℤ) : ℤ × ℤ :=
  (rd u v * P.1 - rc u v * P.2, -(v : ℤ) * P.1 + u * P.2)

lemma gz_ginv {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) (P : ℤ × ℤ) :
    gz u v (ginv u v P) = P := by
  have h := rdet hu hcop
  unfold gz ginv
  ext <;> dsimp only
  · linear_combination P.1 * h
  · linear_combination P.2 * h

lemma ginv_gz {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) (z : ℤ × ℤ) :
    ginv u v (gz u v z) = z := by
  have h := rdet hu hcop
  unfold gz ginv
  ext <;> dsimp only
  · linear_combination z.1 * h
  · linear_combination z.2 * h

lemma detZ_gz {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) (z z' : ℤ × ℤ) :
    detZ (gz u v z) (gz u v z') = detZ z z' := by
  have h := rdet hu hcop
  unfold detZ gz; dsimp only
  linear_combination (z.1 * z'.2 - z.2 * z'.1) * h

lemma gz_e1 (u v : ℕ) : gz u v (1, 0) = ((u : ℤ), (v : ℤ)) := by
  unfold gz; simp

lemma ginv_P0 {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) :
    ginv u v ((u : ℤ), (v : ℤ)) = (1, 0) := by
  rw [← gz_e1, ginv_gz hu hcop]

lemma isCoprime_gz_iff {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) (z : ℤ × ℤ) :
    IsCoprime (gz u v z).1 (gz u v z).2 ↔ IsCoprime z.1 z.2 := by
  have h := rdet hu hcop
  constructor
  · rintro ⟨a, b, hab⟩
    refine ⟨a * u + b * v, a * rc u v + b * rd u v, ?_⟩
    unfold gz at hab; dsimp only at hab
    linear_combination hab
  · rintro ⟨a, b, hab⟩
    refine ⟨a * rd u v - b * v, -(a * rc u v) + b * u, ?_⟩
    unfold gz; dsimp only
    linear_combination ((u : ℤ) * rd u v - rc u v * v) * hab + h

lemma gcd_gz_eq_one_iff {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) (z : ℤ × ℤ) :
    Int.gcd (gz u v z).1 (gz u v z).2 = 1 ↔ Int.gcd z.1 z.2 = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one, ← Int.isCoprime_iff_gcd_eq_one, isCoprime_gz_iff hu hcop]

/-- The box condition at the root of `P₀` is the box condition on `g z`. -/
lemma inBox_iff (P : MemParams) {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) (z : ℤ × ℤ) :
    P.InBox (rootOf (u, v)) z ↔
      P.U ≤ ((gz u v z).1 : ℝ) ∧ ((gz u v z).1 : ℝ) ≤ 16 * P.U ∧
        P.V ≤ ((gz u v z).2 : ℝ) ∧ ((gz u v z).2 : ℝ) ≤ 2 * P.V := by
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  have hd := u_mul_rd hu hcop
  have hd' : (u : ℝ) * (rd u v : ℝ) = 1 + v * (rc u v : ℝ) := by exact_mod_cast hd
  have hr : rootRatio u v = (rc u v : ℝ) / u := by
    unfold rootRatio rc; push_cast; rfl
  have e1 : (rootOf (u, v)).1 * tauR (rootOf (u, v)) z = ((gz u v z).1 : ℝ) := by
    unfold tauR rootOf gz; dsimp only; rw [hr]; push_cast; field_simp
  have e2 : (rootOf (u, v)).2.1 * tauR (rootOf (u, v)) z + z.2 / (rootOf (u, v)).1 =
      ((gz u v z).2 : ℝ) := by
    unfold tauR rootOf gz; dsimp only; rw [hr]; push_cast
    have : (rd u v : ℝ) = (1 + v * (rc u v : ℝ)) / u := by
      rw [eq_div_iff hu'.ne']; linarith
    rw [this]; field_simp; ring
  unfold MemParams.InBox
  rw [e1, e2]

/-! ## Goodness is invariant under integer shifts of the ratio -/

lemma circNorm_add_int (t : ℝ) (n : ℤ) : circNorm (t + n) = circNorm t := by
  unfold circNorm
  rw [round_add_intCast]; push_cast; ring_nf

lemma isGoodRatio_add_int (x Y : ℝ) {K M : ℕ} (a : Fin K → ℝ) (ℓ : Fin K → Fin M → ℕ)
    (r : ℝ) (n : ℤ) : IsGoodRatio x Y a ℓ (r + n) ↔ IsGoodRatio x Y a ℓ r := by
  classical
  have key1 : ∀ m : ℕ, circNorm ((m : ℝ) * (r + n)) = circNorm ((m : ℝ) * r) := by
    intro m
    rw [mul_add, show (m : ℝ) * n = ((m * n : ℤ) : ℝ) by push_cast; ring, circNorm_add_int]
  have key2 : ∀ m : ℤ, circNorm ((m : ℝ) * (r + n)) = circNorm ((m : ℝ) * r) := by
    intro m
    rw [mul_add, show (m : ℝ) * n = ((m * n : ℤ) : ℝ) by push_cast; ring, circNorm_add_int]
  have hsep : ∀ I i₀ T, SepFails x a ℓ I i₀ T (r + n) ↔ SepFails x a ℓ I i₀ T r := by
    intro I i₀ T; unfold SepFails; simp only [key2]
  unfold IsGoodRatio GoodTestOne GoodTestTwo
  have hsum : ∀ (I : Finset (Fin K)) (hI : I.Nonempty),
      (∑ T ∈ freshTuples x a I, freshWeight x a I T *
        if SepFails x a ℓ I (I.max' hI) T (r + n) then (1 : ℝ) else 0) =
      ∑ T ∈ freshTuples x a I, freshWeight x a I T *
        if SepFails x a ℓ I (I.max' hI) T r then (1 : ℝ) else 0 := fun I hI =>
    sum_congr rfl fun T _ => by
      congr 1
      by_cases h : SepFails x a ℓ I (I.max' hI) T r
      · rw [if_pos ((hsep _ _ _).2 h), if_pos h]
      · rw [if_neg (fun h' => h ((hsep _ _ _).1 h')), if_neg h]
  simp only [key1, hsum]

/-! ## The ratio of `g z` -/

lemma detZ_complVec {z : ℤ × ℤ} (hz : Int.gcd z.1 z.2 = 1) : detZ z (complVec z) = 1 := by
  unfold detZ complVec; dsimp only
  have := Int.gcd_eq_gcd_ab z.1 z.2
  rw [hz] at this; push_cast at this
  linarith

/-- The ratio at the root of `P₀` of a primitive `z` differs from the physical ratio of the
position `g z = (P₁, P₂)` by an integer. -/
lemma ratioAt_sub_rootRatio {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) {z : ℤ × ℤ}
    (hz : Int.gcd z.1 z.2 = 1) {P₁ P₂ : ℕ} (hP : gz u v z = ((P₁ : ℤ), (P₂ : ℤ))) (hP₁ : 0 < P₁) :
    ∃ n : ℤ, ratioAt (rootOf (u, v)) z = rootRatio P₁ P₂ + n := by
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  have hP₁' : (0 : ℝ) < P₁ := by exact_mod_cast hP₁
  set w := complVec z
  set W := gz u v w
  have hr : rootRatio u v = (rc u v : ℝ) / u := by unfold rootRatio rc; push_cast; rfl
  have htau : ∀ y : ℤ × ℤ, (u : ℝ) * tauR (rootOf (u, v)) y = ((gz u v y).1 : ℝ) := by
    intro y; unfold tauR rootOf gz; dsimp only; rw [hr]; push_cast; field_simp
  have hratio : ratioAt (rootOf (u, v)) z = (W.1 : ℝ) / P₁ := by
    unfold ratioAt
    have h1 := htau z
    have h2 := htau w
    rw [hP] at h1
    simp only at h1
    rw [show tauR (rootOf (u, v)) w = (W.1 : ℝ) / u by rw [eq_div_iff hu'.ne', mul_comm]; exact h2,
      show tauR (rootOf (u, v)) z = (P₁ : ℝ) / u by rw [eq_div_iff hu'.ne', mul_comm]; exact h1]
    field_simp
  -- `P₁ W₂ − P₂ W₁ = 1`
  have hdet : (P₁ : ℤ) * W.2 - P₂ * W.1 = 1 := by
    have := detZ_gz hu hcop z w
    rw [detZ_complVec hz, hP] at this
    unfold detZ at this; exact this
  have hcopP : Nat.Coprime P₁ P₂ :=
    Nat.isCoprime_iff_coprime.1 ⟨W.2, -W.1, by linear_combination hdet⟩
  have : NeZero P₁ := ⟨hP₁.ne'⟩
  -- `W₁ ≡ c_P (mod P₁)`
  set cP : ℕ := (-(P₂ : ZMod P₁)⁻¹ : ZMod P₁).val with hcP
  have hcong : (P₁ : ℤ) ∣ W.1 - cP := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have h1 : ((P₁ : ℤ) * W.2 - P₂ * W.1 : ZMod P₁) = 1 := by exact_mod_cast congrArg (Int.cast (R := ZMod P₁)) hdet
    push_cast at h1
    rw [ZMod.natCast_self, zero_mul, zero_sub] at h1
    have hunit : (P₂ : ZMod P₁) * (P₂ : ZMod P₁)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one P₂ hcopP.symm
    push_cast
    rw [hcP, ZMod.natCast_zmod_val]
    have : (W.1 : ZMod P₁) = -(P₂ : ZMod P₁)⁻¹ := by
      have e : (W.1 : ZMod P₁) = (P₂ : ZMod P₁)⁻¹ * ((P₂ : ZMod P₁) * W.1) := by
        rw [← mul_assoc, mul_comm ((P₂ : ZMod P₁)⁻¹), hunit, one_mul]
      rw [e, show (P₂ : ZMod P₁) * W.1 = -1 by linear_combination -h1]
      ring
    rw [this]; ring
  obtain ⟨n, hn⟩ := hcong
  refine ⟨n, ?_⟩
  rw [hratio]
  unfold rootRatio
  rw [← hcP]
  have : (W.1 : ℝ) = cP + P₁ * n := by
    have : W.1 = cP + P₁ * n := by linarith
    exact_mod_cast this
  rw [this]; field_simp

/-- Goodness at the root of `P₀` equals physical goodness at `g z`. -/
lemma goodAt_iff (P : MemParams) {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) {z : ℤ × ℤ}
    (hz : Int.gcd z.1 z.2 = 1) {P₁ P₂ : ℕ} (hP : gz u v z = ((P₁ : ℤ), (P₂ : ℤ))) (hP₁ : 0 < P₁)
    (ℓ : P.Lst) :
    P.GoodAt (rootOf (u, v)) z ℓ ↔ IsGoodRatio P.x P.Y P.a ℓ (rootRatio P₁ P₂) := by
  obtain ⟨n, hn⟩ := ratioAt_sub_rootRatio hu hcop hz hP hP₁
  unfold MemParams.GoodAt
  rw [hn, isGoodRatio_add_int]

/-! ## The damping count -/

lemma physDelta_iff (u v p : ℕ) (z : ℤ × ℤ) : physDelta (u, v) p z ↔ (p : ℤ) ∣ (gz u v z).1 :=
  Iff.rfl

/-- The entries of a list. -/
def entrySet {K J : ℕ} (ℓ : Fin K → Fin (J + 1) → ℕ) : Finset ℕ :=
  univ.biUnion fun i => univ.image (ℓ i)

lemma mem_entrySet {K J : ℕ} (ℓ : Fin K → Fin (J + 1) → ℕ) (p : ℕ) :
    p ∈ entrySet ℓ ↔ ∃ i k, ℓ i k = p := by
  simp [entrySet]

lemma card_entrySet (P : MemParams) (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))
    (ℓ : P.Lst) (hℓ : ℓ ∈ listCands P.x P.a P.J) (hinj : ∀ i, Function.Injective (ℓ i)) :
    (entrySet ℓ).card = P.K * (P.J + 1) := by
  simp only [listCands, Fintype.mem_piFinset] at hℓ
  unfold entrySet
  rw [card_biUnion]
  · simp [card_image_of_injective _ (hinj _)]
  · intro i _ i' _ hii'
    rw [Function.onFun, disjoint_left]
    intro p hp hp'
    simp only [mem_image, mem_univ, true_and] at hp hp'
    obtain ⟨k, rfl⟩ := hp
    obtain ⟨k', hk'⟩ := hp'
    have h1 : ℓ i k ∈ P.grp i := hℓ i k
    have h2 : ℓ i k ∈ P.grp i' := hk' ▸ hℓ i' k'
    exact disjoint_left.1 (hdisj i i' hii') h1 h2

lemma card_gPrimes_dvd (P : MemParams) (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))
    (n : ℕ) : (P.gPrimes.filter (· ∣ n)).card = markOmega P.x P.a n := by
  unfold markOmega groupOmega MemParams.gPrimes groupPrimes
  rw [filter_biUnion]
  exact card_biUnion (fun i _ i' _ hii' => disjoint_filter_filter (hdisj i i' hii'))

/-- At a physical state the visit factor is `q_j^{ω(P₁) − KM}`. -/
lemma visitFac_phys (P : MemParams) (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))
    {u v : ℕ} (j : ℕ) (z : ℤ × ℤ) {P₁ : ℕ} (hP : (gz u v z).1 = P₁) (ℓ : P.Lst)
    (hℓ : ℓ ∈ listCands P.x P.a P.J) (hinj : ∀ i, Function.Injective (ℓ i))
    (hdvd : ∀ i k, ℓ i k ∣ P₁) :
    P.visitFac (physDelta (u, v)) j (z, ℓ) = P.qv j ^ excessOmega P.x P.a P.J P₁ := by
  classical
  have hE : entrySet ℓ ⊆ P.gPrimes.filter (· ∣ P₁) := by
    intro p hp
    rw [mem_entrySet] at hp
    obtain ⟨i, k, rfl⟩ := hp
    simp only [listCands, Fintype.mem_piFinset] at hℓ
    simp only [mem_filter, MemParams.gPrimes, groupPrimes, mem_biUnion, mem_univ, true_and]
    exact ⟨⟨i, hℓ i k⟩, hdvd i k⟩
  have hfac : ∀ p ∈ P.gPrimes, P.primeFac (physDelta (u, v)) j p (z, ℓ) =
      if p ∉ entrySet ℓ ∧ p ∣ P₁ then P.qv j else 1 := by
    intro p _
    unfold MemParams.primeFac
    rw [physDelta_iff, hP]
    have hiff : (∃ i k, ℓ i k = p) ↔ p ∈ entrySet ℓ := (mem_entrySet ℓ p).symm
    by_cases hp : p ∈ entrySet ℓ
    · have hd : p ∣ P₁ := (mem_filter.1 (hE hp)).2
      rw [if_pos (hiff.2 hp), if_pos (Int.natCast_dvd_natCast.2 hd), if_neg (fun h => h.1 hp)]
    · rw [if_neg (fun h => hp (hiff.1 h))]
      by_cases hd : p ∣ P₁
      · rw [if_pos (Int.natCast_dvd_natCast.2 hd), if_pos ⟨hp, hd⟩]
      · rw [if_neg (fun h => hd (Int.natCast_dvd_natCast.1 h)), if_neg (fun h => hd h.2)]
  unfold MemParams.visitFac
  rw [prod_congr rfl hfac, prod_ite, prod_const, prod_const_one, mul_one]
  congr 1
  -- the count
  have hsplit : (P.gPrimes.filter fun p => p ∉ entrySet ℓ ∧ p ∣ P₁) =
      P.gPrimes.filter (· ∣ P₁) \ entrySet ℓ := by
    ext p; simp only [mem_filter, mem_sdiff]; tauto
  rw [hsplit, card_sdiff_of_subset hE, card_gPrimes_dvd P hdisj, card_entrySet P hdisj ℓ hℓ hinj]
  rfl

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the physical chain (for D7p)

* goodness is invariant under slot permutations (`isGoodRatio_perm`);
* `G` and `S` are self-adjoint idempotents that commute, so with `X = G S`,
  `A = X T X`, `A* = X T* X` and `(A A*)^R = (X T X T*)^R X` (`opA_pow_eq`);
* the physical chain `physV k` (`X T'_{N−k} X ⋯ T'_{N−1} X u`, `T'_j = T` or `T*` by parity) and
  `((AA*)^R) u = physV N` (`mulVec_opA_pow`). -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset
open scoped Matrix

/-! ## Slot permutations -/

lemma omitProd_perm {K M : ℕ} (ℓ : Fin K → Fin M → ℕ) (pr : Fin K → Equiv.Perm (Fin M))
    (o : Fin K → Fin M) :
    omitProd (fun i => ℓ i ∘ pr i) o = omitProd ℓ (fun i => pr i (o i)) := by
  unfold omitProd
  refine prod_congr rfl fun i _ => ?_
  have : (univ.erase (o i)).map (pr i).toEmbedding = univ.erase (pr i (o i)) := by
    ext j
    simp only [mem_map_equiv, mem_erase, mem_univ, and_true]
    rw [ne_eq, ne_eq, Equiv.symm_apply_eq]
  rw [← this, prod_map]
  rfl

lemma isGoodRatio_perm (x Y : ℝ) {K M : ℕ} (a : Fin K → ℝ) (ℓ : Fin K → Fin M → ℕ)
    (pr : Fin K → Equiv.Perm (Fin M)) (r : ℝ) :
    IsGoodRatio x Y a (fun i => ℓ i ∘ pr i) r ↔ IsGoodRatio x Y a ℓ r := by
  classical
  set e : (Fin K → Fin M) ≃ (Fin K → Fin M) := Equiv.piCongrRight pr with he
  have he' : ∀ o, e o = fun i => pr i (o i) := fun o => rfl
  have h1 : GoodTestOne Y (fun i => ℓ i ∘ pr i) r ↔ GoodTestOne Y ℓ r := by
    unfold GoodTestOne
    simp only [omitProd_perm]
    constructor
    · intro h o l hl1 hl2
      have := h (e.symm o) l hl1 hl2
      rwa [show (fun i => pr i (e.symm o i)) = o from by
        rw [← he' (e.symm o), Equiv.apply_symm_apply]] at this
    · intro h o l hl1 hl2; exact h _ l hl1 hl2
  have hsep : ∀ I i₀ T, SepFails x a (fun i => ℓ i ∘ pr i) I i₀ T r ↔ SepFails x a ℓ I i₀ T r := by
    intro I i₀ T
    unfold SepFails
    simp only [omitProd_perm]
    constructor
    · rintro ⟨o, o', Z, Z', h⟩; exact ⟨_, _, Z, Z', h⟩
    · rintro ⟨o, o', Z, Z', h⟩
      refine ⟨e.symm o, e.symm o', Z, Z', ?_⟩
      rwa [show (fun i => pr i (e.symm o i)) = o from by
          rw [← he' (e.symm o), Equiv.apply_symm_apply],
        show (fun i => pr i (e.symm o' i)) = o' from by
          rw [← he' (e.symm o'), Equiv.apply_symm_apply]]
  have h2 : GoodTestTwo x a (fun i => ℓ i ∘ pr i) r ↔ GoodTestTwo x a ℓ r := by
    unfold GoodTestTwo
    have hsum : ∀ (I : Finset (Fin K)) (hI : I.Nonempty),
        (∑ T ∈ freshTuples x a I, freshWeight x a I T *
          if SepFails x a (fun i => ℓ i ∘ pr i) I (I.max' hI) T r then (1 : ℝ) else 0) =
        ∑ T ∈ freshTuples x a I, freshWeight x a I T *
          if SepFails x a ℓ I (I.max' hI) T r then (1 : ℝ) else 0 := fun I hI =>
      sum_congr rfl fun T _ => by
        congr 1
        by_cases h : SepFails x a ℓ I (I.max' hI) T r
        · rw [if_pos ((hsep _ _ _).2 h), if_pos h]
        · rw [if_neg (fun h' => h ((hsep _ _ _).1 h')), if_neg h]
    simp only [hsum]
  unfold IsGoodRatio
  rw [h1, h2]

/-- Injective lists with the same range differ by a permutation. -/
lemma exists_perm_of_range_eq {M : ℕ} (f g : Fin M → ℕ) (hf : Function.Injective f)
    (hg : Function.Injective g) (h : Set.range g = Set.range f) :
    ∃ σ : Equiv.Perm (Fin M), g = f ∘ σ := by
  have hmem : ∀ k, g k ∈ Set.range f := fun k => h ▸ Set.mem_range_self k
  set e := Equiv.ofInjective f hf
  set σ : Fin M → Fin M := fun k => e.symm ⟨g k, hmem k⟩
  have hσ : ∀ k, f (σ k) = g k := by
    intro k
    have := e.apply_symm_apply ⟨g k, hmem k⟩
    exact congrArg Subtype.val this
  have hinj : Function.Injective σ := by
    intro k k' hkk
    apply hg
    rw [← hσ k, ← hσ k', hkk]
  refine ⟨Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hinj), ?_⟩
  funext k
  exact (hσ k).symm

/-! ## The physical matrices -/

section Phys

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {A₀ Y : ℝ} {J d₀ : ℕ} {U V : ℝ}

lemma goodProj_conjTranspose : (goodProj x Y a J U V)ᴴ = goodProj x Y a J U V := by
  unfold goodProj
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext s
  rw [Pi.star_apply]
  split_ifs <;> simp

lemma orbRel_good {s t : PhysState x a J U V} (h : orbRel s t) :
    IsGoodRatio x Y a s.1.2 (rootRatio s.1.1.1 s.1.1.2) ↔
      IsGoodRatio x Y a t.1.2 (rootRatio t.1.1.1 t.1.1.2) := by
  have hs := (mem_filter.1 s.2).2.1
  have ht := (mem_filter.1 t.2).2.1
  have hperm : ∀ i, ∃ σ : Equiv.Perm (Fin (J + 1)), t.1.2 i = s.1.2 i ∘ σ :=
    fun i => exists_perm_of_range_eq _ _ (hs i) (ht i) (h.2 i)
  choose σ hσ using hperm
  have : t.1.2 = fun i => s.1.2 i ∘ σ i := funext hσ
  rw [this, h.1, isGoodRatio_perm]

open Classical in
lemma slotSym_symm (s s' : PhysState x a J U V) :
    slotSym x a J U V s s' = slotSym x a J U V s' s := by
  simp only [slotSym_apply]
  by_cases h : orbRel s s'
  · rw [if_pos h, if_pos (orbRel_symm h), orbit_card_eq h]
  · rw [if_neg h, if_neg (fun h' => h (orbRel_symm h'))]

lemma slotSym_conjTranspose : (slotSym x a J U V)ᴴ = slotSym x a J U V := by
  ext s s'
  rw [Matrix.conjTranspose_apply, slotSym_symm]
  unfold slotSym
  split_ifs <;> simp

open Classical in
lemma slotSym_mul_self : slotSym x a J U V * slotSym x a J U V = slotSym x a J U V := by
  ext s s''
  rw [Matrix.mul_apply]
  simp only [slotSym_apply]
  have hpos : 0 < (univ.filter fun t => orbRel s t).card :=
    card_pos.2 ⟨s, mem_filter.2 ⟨mem_univ _, rfl, fun i => rfl⟩⟩
  have hn : ((univ.filter fun t => orbRel s t).card : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  set n := ((univ.filter fun t => orbRel s t).card : ℂ)
  have hterm : ∀ t, (if orbRel s t then n⁻¹ else 0) *
      (if orbRel t s'' then ((univ.filter fun t' => orbRel t t').card : ℂ)⁻¹ else 0) =
      if orbRel s t then (if orbRel s s'' then n⁻¹ * n⁻¹ else 0) else 0 := by
    intro t
    by_cases ht : orbRel s t
    · rw [if_pos ht, if_pos ht, ← orbit_card_eq ht]
      by_cases hs : orbRel s s''
      · rw [if_pos (orbRel_trans (orbRel_symm ht) hs), if_pos hs]
      · rw [if_neg (fun h' => hs (orbRel_trans ht h')), if_neg hs, mul_zero]
    · rw [if_neg ht, if_neg ht, zero_mul]
  simp_rw [hterm]
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  by_cases hs : orbRel s s''
  · rw [if_pos hs, if_pos hs]
    change n * (n⁻¹ * n⁻¹) = n⁻¹
    field_simp
  · rw [if_neg hs, if_neg hs, mul_zero]

lemma goodProj_mul_self : goodProj x Y a J U V * goodProj x Y a J U V = goodProj x Y a J U V := by
  unfold goodProj
  rw [Matrix.diagonal_mul_diagonal]
  congr 1; funext s; split_ifs <;> simp

open Classical in
lemma goodProj_slotSym_comm :
    goodProj x Y a J U V * slotSym x a J U V = slotSym x a J U V * goodProj x Y a J U V := by
  ext s s'
  unfold goodProj
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : slotSym x a J U V s s' = 0
  · rw [h, mul_zero, zero_mul]
  · have hrel : orbRel s s' := by
      by_contra hc; apply h; rw [slotSym_apply, if_neg hc]
    rw [mul_comm]
    congr 1
    by_cases hg : IsGoodRatio x Y a s.1.2 (rootRatio s.1.1.1 s.1.1.2)
    · rw [if_pos hg, if_pos ((orbRel_good (Y := Y) hrel).1 hg)]
    · rw [if_neg hg, if_neg (fun h' => hg ((orbRel_good (Y := Y) hrel).2 h'))]

/-- `X = G S`. -/
noncomputable def physX (x Y : ℝ) {K : ℕ} (a : Fin K → ℝ) (J : ℕ) (U V : ℝ) :
    Matrix (PhysState x a J U V) (PhysState x a J U V) ℂ :=
  goodProj x Y a J U V * slotSym x a J U V

lemma physX_mul_self : physX x Y a J U V * physX x Y a J U V = physX x Y a J U V := by
  unfold physX
  calc goodProj x Y a J U V * slotSym x a J U V * (goodProj x Y a J U V * slotSym x a J U V) =
      goodProj x Y a J U V * (slotSym x a J U V * goodProj x Y a J U V) * slotSym x a J U V := by
        simp only [Matrix.mul_assoc]
    _ = goodProj x Y a J U V * (goodProj x Y a J U V * slotSym x a J U V) * slotSym x a J U V := by
        rw [goodProj_slotSym_comm]
    _ = goodProj x Y a J U V * slotSym x a J U V := by
        rw [← Matrix.mul_assoc, goodProj_mul_self, Matrix.mul_assoc, slotSym_mul_self]

lemma opA_eq : opA x a A₀ Y J d₀ U V =
    physX x Y a J U V * rowOp x a A₀ Y J d₀ U V * physX x Y a J U V := by
  unfold opA physX
  simp only [Matrix.mul_assoc]
  rw [← goodProj_slotSym_comm]

lemma opA_conjTranspose : (opA x a A₀ Y J d₀ U V)ᴴ =
    physX x Y a J U V * (rowOp x a A₀ Y J d₀ U V)ᴴ * physX x Y a J U V := by
  unfold opA physX
  simp only [Matrix.conjTranspose_mul, goodProj_conjTranspose, slotSym_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← goodProj_slotSym_comm]

/-- `(A A*)^R = (X T X T*)^R X` for `R ≥ 1`. -/
lemma opA_pow_eq {R : ℕ} (hR : 1 ≤ R) :
    (opA x a A₀ Y J d₀ U V * (opA x a A₀ Y J d₀ U V)ᴴ) ^ R =
      (physX x Y a J U V * rowOp x a A₀ Y J d₀ U V * physX x Y a J U V *
        (rowOp x a A₀ Y J d₀ U V)ᴴ) ^ R * physX x Y a J U V := by
  set X := physX x Y a J U V
  set T := rowOp x a A₀ Y J d₀ U V
  set Yc := X * T * X * Tᴴ
  have hXX : X * X = X := physX_mul_self
  have hAA : opA x a A₀ Y J d₀ U V * (opA x a A₀ Y J d₀ U V)ᴴ = Yc * X := by
    rw [opA_conjTranspose, opA_eq]
    calc X * T * X * (X * Tᴴ * X) = X * T * (X * X) * Tᴴ * X := by simp only [Matrix.mul_assoc]
      _ = Yc * X := by rw [hXX]
  have hXY : X * Yc = Yc := by
    calc X * Yc = (X * X) * T * X * Tᴴ := by simp only [Yc, Matrix.mul_assoc]
      _ = Yc := by rw [hXX]
  rw [hAA]
  obtain ⟨R', rfl⟩ := Nat.exists_eq_add_of_le' hR
  induction R' with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih (by omega), pow_succ]
    calc Yc ^ (n + 1) * X * (Yc * X) = Yc ^ (n + 1) * (X * Yc) * X := by
          simp only [Matrix.mul_assoc]
      _ = Yc ^ (n + 1) * Yc * X := by rw [hXY]

/-- `T'_j`: `T` on even edges, `T*` on odd edges. -/
noncomputable def physT (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (A₀ Y : ℝ) (J d₀ : ℕ) (U V : ℝ) (j : ℕ) :
    Matrix (PhysState x a J U V) (PhysState x a J U V) ℂ :=
  if Even j then rowOp x a A₀ Y J d₀ U V else (rowOp x a A₀ Y J d₀ U V)ᴴ

/-- The physical chain from the end: `physV N u k = X T'_{N−k} X ⋯ T'_{N−1} X u`. -/
noncomputable def physV (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (A₀ Y : ℝ) (J d₀ : ℕ) (U V : ℝ) (N : ℕ)
    (u : PhysState x a J U V → ℂ) : ℕ → (PhysState x a J U V → ℂ)
  | 0 => (physX x Y a J U V).mulVec u
  | k + 1 => (physX x Y a J U V).mulVec
      ((physT x a A₀ Y J d₀ U V (N - (k + 1))).mulVec (physV x a A₀ Y J d₀ U V N u k))

lemma physV_two {R : ℕ} (u : PhysState x a J U V → ℂ) (k : ℕ) (hk : k ≤ R) :
    physV x a A₀ Y J d₀ U V (2 * R) u (2 * k) =
      ((physX x Y a J U V * rowOp x a A₀ Y J d₀ U V * physX x Y a J U V *
        (rowOp x a A₀ Y J d₀ U V)ᴴ) ^ k).mulVec ((physX x Y a J U V).mulVec u) := by
  induction k with
  | zero => simp [physV]
  | succ n ih =>
    have h1 : 2 * (n + 1) = (2 * n + 1) + 1 := by ring
    rw [h1]
    simp only [physV]
    rw [ih (by omega)]
    have hev : Even (2 * R - (2 * n + 1 + 1)) := by
      rw [show 2 * R - (2 * n + 1 + 1) = 2 * (R - n - 1) by omega]; exact even_two_mul _
    have hodd : ¬ Even (2 * R - (2 * n + 1)) := by
      rw [show 2 * R - (2 * n + 1) = 2 * (R - n - 1) + 1 by omega, Nat.not_even_iff_odd]
      exact odd_two_mul_add_one _
    simp only [physT, if_pos hev, if_neg hodd, Matrix.mulVec_mulVec]
    rw [pow_succ']
    simp only [Matrix.mul_assoc]

/-- `((A A*)^R) u` is the physical chain. -/
lemma mulVec_opA_pow {R : ℕ} (hR : 1 ≤ R) (u : PhysState x a J U V → ℂ) :
    ((opA x a A₀ Y J d₀ U V * (opA x a A₀ Y J d₀ U V)ᴴ) ^ R).mulVec u =
      physV x a A₀ Y J d₀ U V (2 * R) u (2 * R) := by
  rw [opA_pow_eq hR, ← Matrix.mulVec_mulVec, physV_two u R le_rfl]

end Phys

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the cuts of D7 (the moment (4.1)) and the reduction

Seven statements about the draft model `L102D_OpDefs` + `L102D_MemDefs`, in the order of the
proof of [21] Proposition 4.1:

* `PathExpansionStmt` (D7p, exact): the physical moment is the sum over primitive roots `P₀` of
  the path functional in root coordinates, [21] §3.5 (3.30)–(3.32).
* `RootReplacementStmt` (D7r, [21] Lemma 3.4): the sum over roots is `UV/ζ(2)` times the integral
  of the independent-line moment over `[1,16] × [1,2] × [0,1]`, up to `UV L^{-AN}`.
* `MemoryIdentityStmt` (D7a, exact, [21] (4.5)–(4.15)): the independent-line moment is the
  baseline times the memory moment with global birth distinctness (no truncation).
* `TruncationStmt` (D7b, [21] (4.16)): truncating the memory at `B = ⌈L²⌉` costs `L^{-AN}`.
* `GhostBoundStmt` (D7c, [21] (4.19)–(4.22)): `‖G_j‖ ≤ C_K` on `H_B`.
* `EdgeBoundStmt` (D7d, [21] (4.23)–(4.42)): `‖E_j‖ ≤ L^{-G}` on `H_B`, `A₀` and then `K` large.
* `DistinctnessStmt` (D7e, [21] (4.43)–(4.55)): given D7c and D7d, the truncated memory moment
  with global birth distinctness is `≤ L^{-(G-1)N}`.

`moment_bound_of_cuts` proves `MomentBoundStmt` (D7) from them. -/

-- `MemParams.RootIn` now lives in the bundle `Def_ArtinMemoryModel` (round 5).

namespace ArtinPrimitiveRoots.L102D

open Real Finset

/-- **D7p** (exact path expansion in root coordinates). For disjoint groups, `R ≥ 1` and
`U, V ≥ 1`, the physical moment `∑_P ⟨u_P, (AA*)^R u_P⟩_σ` equals the sum over the primitive
roots `P₀ ∈ Ω` of the path functional at the root `P₀` with physical divisibility. -/
def PathExpansionStmt : Prop :=
  ∀ (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (A₀ Y : ℝ) (J R d₀ : ℕ) (U V : ℝ) (B : ℕ),
    (∀ i i', i ≠ i' → Disjoint (primeGroup x (a i)) (primeGroup x (a i'))) →
    1 ≤ R → 1 ≤ U → 1 ≤ V →
    momentSum x a A₀ Y J R d₀ U V =
      ∑ P₀ ∈ posBox U V,
        (⟨x, K, a, A₀, Y, J, 2 * R, d₀, U, V, B⟩ : MemParams).pathPhi (rootOf P₀) (physDelta P₀)

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: D7p, the exact path expansion in root coordinates

`path_expansion : PathExpansionStmt`. For each primitive root `P₀ = (u, v)` the physical chain
`X T X T* ⋯ X u_{P₀}` is pulled back along `P = g z` to `physTail` at the root `rootOf P₀` with
the divisibility oracle `physDelta P₀`: the damping `(1/2)^{ω−KM}` of each edge endpoint becomes
the visit factor `q_j^{ω−KM}` (`visitFac_phys`), goodness transfers by `goodAt_iff`, the slot
symmetrization is the average over list permutations, and the edge sum over physical targets is
the sum over `(z', new labels)` (`edge_corr`). -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset
open scoped Matrix

section PhysHelpers

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {A₀ Y : ℝ} {J d₀ : ℕ} {U V : ℝ}

lemma listProd_eq_pad_mul_last {K J : ℕ} (ℓ : Fin K → Fin (J + 1) → ℕ) :
    listProd ℓ = padProd ℓ * lastProd ℓ := by
  unfold listProd padProd lastProd
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [Fin.prod_univ_castSucc]

lemma padProd_dvd_pos (hdisj : ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)))
    (s : PhysState x a J U V) : padProd s.1.2 ∣ s.1.1.1 :=
  (Dvd.intro _ (listProd_eq_pad_mul_last s.1.2).symm).trans (listProd_dvd_of_disjoint hdisj s)

open Classical in
/-- The row operation without its damping factor. -/
noncomputable def rowOp0 (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (A₀ Y : ℝ) (J d₀ : ℕ) (U V : ℝ)
    (s s' : PhysState x a J U V) : ℂ :=
  if (∀ i (j : Fin J), s'.1.2 i j.castSucc = s.1.2 i j.castSucc) ∧
      (∀ i, s'.1.2 i (Fin.last J) ∉ Set.range (s.1.2 i)) ∧
      d₀ ≤ padProd s.1.2 ∧ padProd s.1.2 < 2 * d₀ then
    (((∏ i, (groupReciprocalSum x (a i))⁻¹) * ((d₀ : ℝ) / padProd s.1.2) *
        dyadicBump ((lastProd s.1.2 : ℝ) / Y) * dyadicBump ((lastProd s'.1.2 : ℝ) / Y) : ℝ) : ℂ) *
      minorKernel x A₀ Y
        (((s.1.1.1 : ℤ) * s'.1.1.2 - (s.1.1.2 : ℤ) * s'.1.1.1) / (padProd s.1.2 : ℤ))
        (lastProd s'.1.2) (lastProd s.1.2)
  else 0

/-- The half damping `(1/2)^{ω(P₁) − KM}` of a state. -/
noncomputable def halfDamp (s : PhysState x a J U V) : ℝ := (1 / 2 : ℝ) ^ excessOmega x a J s.1.1.1

lemma rowOp_eq_damp (s s' : PhysState x a J U V) :
    rowOp x a A₀ Y J d₀ U V s s' =
      ((halfDamp s * halfDamp s' : ℝ) : ℂ) * rowOp0 x a A₀ Y J d₀ U V s s' := by
  unfold rowOp rowOp0 halfDamp
  split_ifs
  · rw [pow_add]; push_cast; ring
  · simp

lemma physT_apply (j : ℕ) (s s' : PhysState x a J U V) :
    physT x a A₀ Y J d₀ U V j s s' = ((halfDamp s * halfDamp s' : ℝ) : ℂ) *
      (if Even j then rowOp0 x a A₀ Y J d₀ U V s s'
        else (starRingEnd ℂ) (rowOp0 x a A₀ Y J d₀ U V s' s)) := by
  unfold physT
  split_ifs
  · exact rowOp_eq_damp s s'
  · simp only [Matrix.conjTranspose_apply, rowOp_eq_damp, star_mul', Complex.star_def,
      Complex.conj_ofReal]
    push_cast; ring

/-- The state with permuted lists. -/
noncomputable def permState (s : PhysState x a J U V) (pr : Fin K → Equiv.Perm (Fin (J + 1))) :
    PhysState x a J U V :=
  ⟨(s.1.1, fun i => s.1.2 i ∘ pr i), by
    have hs := mem_filter.1 s.2
    obtain ⟨hmem, hinj, hdvd⟩ := hs
    refine mem_filter.2 ⟨mem_product.2 ⟨(mem_product.1 hmem).1, ?_⟩, fun i => (hinj i).comp
      (pr i).injective, fun i j => hdvd i (pr i j)⟩
    have hc := (mem_product.1 hmem).2
    simp only [listCands, Fintype.mem_piFinset] at hc ⊢
    exact fun i j => hc i (pr i j)⟩

lemma orbRel_permState (s : PhysState x a J U V) (pr : Fin K → Equiv.Perm (Fin (J + 1))) :
    orbRel s (permState s pr) := by
  refine ⟨rfl, fun i => ?_⟩
  show Set.range (s.1.2 i ∘ pr i) = Set.range (s.1.2 i)
  exact EquivLike.range_comp _ _

lemma permState_injective (s : PhysState x a J U V) :
    Function.Injective (permState s) := by
  intro pr pr' h
  have h2 := congrArg (fun t : PhysState x a J U V => t.1.2) h
  simp only [permState] at h2
  have hinj := (mem_filter.1 s.2).2.1
  funext i
  apply Equiv.ext
  intro k
  exact hinj i (congrFun (congrFun h2 i) k)

open Classical in
/-- The slot symmetrization is the average over list permutations. -/
lemma slotSym_mulVec_eq (φ : PhysState x a J U V → ℂ) (s : PhysState x a J U V) :
    (slotSym x a J U V).mulVec φ s =
      ((((J + 1).factorial ^ K : ℕ) : ℂ))⁻¹ * ∑ pr : Fin K → Equiv.Perm (Fin (J + 1)),
        φ (permState s pr) := by
  -- the orbit is the image of the permutations
  have himg : (univ.filter fun t => orbRel s t) = univ.image (permState s) := by
    ext t
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro ht
      have hs := (mem_filter.1 s.2).2.1
      have ht' := (mem_filter.1 t.2).2.1
      have hperm : ∀ i, ∃ σ : Equiv.Perm (Fin (J + 1)), t.1.2 i = s.1.2 i ∘ σ :=
        fun i => exists_perm_of_range_eq _ _ (hs i) (ht' i) (ht.2 i)
      choose σ hσ using hperm
      refine ⟨σ, Subtype.ext (Prod.ext ht.1.symm (funext fun i => (hσ i).symm))⟩
    · rintro ⟨pr, rfl⟩; exact orbRel_permState s pr
  have hcard : (univ.filter fun t => orbRel s t).card = (J + 1).factorial ^ K := by
    rw [himg, card_image_of_injective _ (permState_injective s), card_univ, Fintype.card_pi,
      prod_const, card_univ, Fintype.card_fin, Fintype.card_perm, Fintype.card_fin]
  simp only [Matrix.mulVec, dotProduct, slotSym_apply]
  rw [show (∑ t, (if orbRel s t then ((univ.filter fun t => orbRel s t).card : ℂ)⁻¹ else 0) * φ t)
      = ((univ.filter fun t => orbRel s t).card : ℂ)⁻¹ * ∑ t ∈ univ.filter (fun t => orbRel s t), φ t
      by rw [mul_sum, sum_filter]; refine sum_congr rfl fun t _ => ?_; split_ifs <;> simp]
  rw [hcard, himg, sum_image fun pr _ pr' _ h => permState_injective s h]

end PhysHelpers

section TailFacts

variable (P : MemParams)

lemma mem_gPrimes_of_grp {i : Fin P.K} {p : ℕ} (hp : p ∈ P.grp i) : p ∈ P.gPrimes := by
  simp only [MemParams.gPrimes, groupPrimes, mem_biUnion, mem_univ, true_and]
  exact ⟨i, hp⟩

lemma visitFac_eq_zero (δ : ℕ → ℤ × ℤ → Prop) (j : ℕ) (z : ℤ × ℤ) (ℓ : P.Lst)
    (hℓ : ∀ i k, ℓ i k ∈ P.grp i) (h : ∃ i k, ¬ δ (ℓ i k) z) : P.visitFac δ j (z, ℓ) = 0 := by
  classical
  obtain ⟨i, k, hk⟩ := h
  unfold MemParams.visitFac
  refine prod_eq_zero (mem_gPrimes_of_grp P (hℓ i k)) ?_
  unfold MemParams.primeFac
  rw [if_pos ⟨i, k, rfl⟩, if_neg hk]

lemma physTail_eq_zero (ω : ℝ × ℝ × ℝ) (δ : ℕ → ℤ × ℤ → Prop) (k : ℕ)
    (f : (ℤ × ℤ) × P.Lst → ℂ) (z : ℤ × ℤ) (ℓ : P.Lst) (hℓ : ∀ i k, ℓ i k ∈ P.grp i)
    (h : ∃ i k, ¬ δ (ℓ i k) z) : P.physTail ω δ k f (z, ℓ) = 0 := by
  cases k with
  | zero => simp only [MemParams.physTail, visitFac_eq_zero P δ _ z ℓ hℓ h]; simp
  | succ k => simp only [MemParams.physTail, visitFac_eq_zero P δ _ z ℓ hℓ h]; simp

lemma visitFac_perm (δ : ℕ → ℤ × ℤ → Prop) (j : ℕ) (z : ℤ × ℤ) (ℓ : P.Lst)
    (σ : Fin P.K → Equiv.Perm (Fin (P.J + 1))) :
    P.visitFac δ j (z, fun i => ℓ i ∘ σ i) = P.visitFac δ j (z, ℓ) := by
  classical
  unfold MemParams.visitFac MemParams.primeFac
  refine prod_congr rfl fun p _ => ?_
  have hiff : (∃ i k, (fun i => ℓ i ∘ σ i) i k = p) ↔ ∃ i k, ℓ i k = p := by
    constructor
    · rintro ⟨i, k, h⟩; exact ⟨i, σ i k, h⟩
    · rintro ⟨i, k, h⟩; exact ⟨i, (σ i).symm k, by simp [h]⟩
  simp only [hiff]

lemma listSym_perm (g : P.Lst → ℂ) (ℓ : P.Lst) (σ : Fin P.K → Equiv.Perm (Fin (P.J + 1))) :
    P.listSym g (fun i => ℓ i ∘ σ i) = P.listSym g ℓ := by
  unfold MemParams.listSym
  congr 1
  let e : (Fin P.K → Equiv.Perm (Fin (P.J + 1))) ≃ (Fin P.K → Equiv.Perm (Fin (P.J + 1))) :=
    Equiv.piCongrRight fun i => Equiv.mulLeft (σ i)
  refine Fintype.sum_equiv e _ _ fun pr => ?_
  congr 1

lemma physTail_perm (ω : ℝ × ℝ × ℝ) (δ : ℕ → ℤ × ℤ → Prop) (k : ℕ)
    (f : (ℤ × ℤ) × P.Lst → ℂ)
    (hf : ∀ z ℓ (σ : Fin P.K → Equiv.Perm (Fin (P.J + 1))), f (z, fun i => ℓ i ∘ σ i) = f (z, ℓ))
    (z : ℤ × ℤ) (ℓ : P.Lst) (σ : Fin P.K → Equiv.Perm (Fin (P.J + 1))) :
    P.physTail ω δ k f (z, fun i => ℓ i ∘ σ i) = P.physTail ω δ k f (z, ℓ) := by
  cases k with
  | zero => simp only [MemParams.physTail, visitFac_perm, hf]
  | succ k =>
    simp only [MemParams.physTail, visitFac_perm]
    rw [show ∀ g : (ℤ × ℤ) × P.Lst → ℂ, P.symP g (z, fun i => ℓ i ∘ σ i) = P.symP g (z, ℓ) from
      fun g => listSym_perm P _ ℓ σ]

lemma symP_physTail (ω : ℝ × ℝ × ℝ) (δ : ℕ → ℤ × ℤ → Prop) (k : ℕ)
    (f : (ℤ × ℤ) × P.Lst → ℂ)
    (hf : ∀ z ℓ (σ : Fin P.K → Equiv.Perm (Fin (P.J + 1))), f (z, fun i => ℓ i ∘ σ i) = f (z, ℓ)) :
    P.symP (P.physTail ω δ k f) = P.physTail ω δ k f := by
  funext s
  unfold MemParams.symP MemParams.listSym
  simp only [physTail_perm P ω δ k f hf]
  rw [sum_const, card_univ, Fintype.card_pi, prod_const, card_univ, Fintype.card_fin,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  have : (((P.J + 1).factorial ^ P.K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
  field_simp

end TailFacts

section Corr

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {A₀ Y : ℝ} {J R d₀ : ℕ} {U V : ℝ} {B : ℕ}

/-- The parameters of D7p. -/
noncomputable abbrev pP (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (A₀ Y : ℝ) (J R d₀ : ℕ) (U V : ℝ)
    (B : ℕ) : MemParams :=
  ⟨x, K, a, A₀, Y, J, 2 * R, d₀, U, V, B⟩

/-- Root coordinates of a physical state at the root `(u, v)`. -/
noncomputable def zOf (u v : ℕ) (s : PhysState x a J U V) : ℤ × ℤ :=
  ginv u v ((s.1.1.1 : ℤ), (s.1.1.2 : ℤ))

open Classical in
/-- Physical goodness of a state. -/
noncomputable def gd (Y : ℝ) (s : PhysState x a J U V) : ℂ :=
  if IsGoodRatio x Y a s.1.2 (rootRatio s.1.1.1 s.1.1.2) then 1 else 0

lemma gz_zOf {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) (s : PhysState x a J U V) :
    gz u v (zOf u v s) = ((s.1.1.1 : ℤ), (s.1.1.2 : ℤ)) := gz_ginv hu hcop _

lemma zOf_gcd {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (s : PhysState x a J U V) : Int.gcd (zOf u v s).1 (zOf u v s).2 = 1 := by
  rw [← gcd_gz_eq_one_iff hu hcop, gz_zOf hu hcop]
  have := (state_pos_bounds (by linarith) (by linarith) s).2.2.1
  simpa [Int.gcd_natCast_natCast] using this

set_option maxRecDepth 100000 in
lemma zOf_mem {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (huU : (u : ℝ) ≤ 16 * U) (hvV : (v : ℝ) ≤ 2 * V) (s : PhysState x a J U V) :
    zOf u v s ∈ (pP x a A₀ Y J R d₀ U V B).zSet := by
  obtain ⟨h1, h2, _, h4, h5⟩ := state_pos_bounds (by linarith) (by linarith) s
  have hc0 := rc_nonneg u v
  have hcu : (rc u v : ℝ) ≤ u := by exact_mod_cast (rc_lt (v := v) hu).le
  have hd := u_mul_rd hu hcop
  have hu' : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hdR : (u : ℝ) * (rd u v : ℝ) = 1 + v * (rc u v : ℝ) := by exact_mod_cast hd
  have hc0R : (0 : ℝ) ≤ rc u v := by exact_mod_cast hc0
  have hd0 : (0 : ℝ) ≤ rd u v := by
    have h : (0 : ℝ) ≤ (u : ℝ) * (rd u v : ℝ) := by rw [hdR]; positivity
    exact (mul_nonneg_iff_of_pos_left (by linarith)).1 h
  have hdv : (rd u v : ℝ) ≤ 1 + v := by
    have : (u : ℝ) * (rd u v : ℝ) ≤ u * (1 + v) := by
      rw [hdR]; nlinarith
    exact le_of_mul_le_mul_left this (by linarith)
  have hv0 : (0 : ℝ) ≤ v := by positivity
  have hP1 : (0 : ℝ) ≤ s.1.1.1 := by positivity
  have hP2 : (0 : ℝ) ≤ s.1.1.2 := by positivity
  have hb1 : |((zOf u v s).1 : ℝ)| ≤ 1000 * U * V + 1000 := by
    unfold zOf ginv; push_cast
    rw [abs_le]
    constructor <;> nlinarith
  have hb2 : |((zOf u v s).2 : ℝ)| ≤ 1000 * U * V + 1000 := by
    unfold zOf ginv; push_cast
    rw [abs_le]
    constructor <;> nlinarith
  have hzm : (1000 * U * V + 1000 : ℝ) ≤ ((pP x a A₀ Y J R d₀ U V B).zMax : ℝ) := by
    unfold MemParams.zMax
    push_cast
    have := Nat.le_ceil (1000 * U * V)
    linarith
  unfold MemParams.zSet
  rw [mem_filter, mem_product, mem_Icc, mem_Icc]
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, zOf_gcd hu hcop hU hV s⟩
  · have := (abs_le.1 (hb1.trans hzm)).1
    have : (-((pP x a A₀ Y J R d₀ U V B).zMax : ℤ) : ℝ) ≤ ((zOf u v s).1 : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · have := (abs_le.1 (hb1.trans hzm)).2
    exact_mod_cast this
  · have := (abs_le.1 (hb2.trans hzm)).1
    have : (-((pP x a A₀ Y J R d₀ U V B).zMax : ℤ) : ℝ) ≤ ((zOf u v s).2 : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · have := (abs_le.1 (hb2.trans hzm)).2
    exact_mod_cast this

lemma inBox_zOf {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (s : PhysState x a J U V) :
    (pP x a A₀ Y J R d₀ U V B).InBox (rootOf (u, v)) (zOf u v s) := by
  rw [inBox_iff _ hu hcop, gz_zOf hu hcop]
  obtain ⟨h1, h2, _, h4, h5⟩ := state_pos_bounds (by linarith) (by linarith) s
  push_cast
  exact ⟨h1, h2, h4, h5⟩

lemma goodAt_zOf {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (s : PhysState x a J U V) (ℓ : Fin K → Fin (J + 1) → ℕ) :
    (pP x a A₀ Y J R d₀ U V B).GoodAt (rootOf (u, v)) (zOf u v s) ℓ ↔
      IsGoodRatio x Y a ℓ (rootRatio s.1.1.1 s.1.1.2) := by
  have hP1 : 0 < s.1.1.1 := by
    have := (state_pos_bounds (by linarith) (by linarith) s).1
    exact_mod_cast (show (0 : ℝ) < s.1.1.1 by linarith)
  exact goodAt_iff (pP x a A₀ Y J R d₀ U V B) hu hcop (zOf_gcd hu hcop hU hV s) (gz_zOf hu hcop s)
    hP1 ℓ

lemma visitFac_zOf {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v)
    (hdisj : ∀ i i', i ≠ i' → Disjoint (primeGroup x (a i)) (primeGroup x (a i'))) (j : ℕ)
    (s : PhysState x a J U V) :
    (pP x a A₀ Y J R d₀ U V B).visitFac (physDelta (u, v)) j (zOf u v s, s.1.2) =
      (pP x a A₀ Y J R d₀ U V B).qv j ^ excessOmega x a J s.1.1.1 := by
  obtain ⟨hmem, hinj, hdvd⟩ := mem_filter.1 s.2
  exact visitFac_phys (pP x a A₀ Y J R d₀ U V B) hdisj j (zOf u v s)
    (by rw [gz_zOf hu hcop]) s.1.2 (mem_product.1 hmem).2 hinj hdvd

set_option maxRecDepth 100000 in
/-- A physical state from root data: a box point `z` of `zSet` and a valid list. -/
lemma exists_state {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) (z : ℤ × ℤ)
    (hz : z ∈ (pP x a A₀ Y J R d₀ U V B).zSet)
    (hbox : (pP x a A₀ Y J R d₀ U V B).InBox (rootOf (u, v)) z) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (ℓ : Fin K → Fin (J + 1) → ℕ) (hℓ : ℓ ∈ listCands x a J) (hinj : ∀ i, Function.Injective (ℓ i))
    (hdvd : ∀ i k, physDelta (u, v) (ℓ i k) z) :
    ∃ s : PhysState x a J U V, zOf u v s = z ∧ s.1.2 = ℓ := by
  rw [inBox_iff _ hu hcop] at hbox
  obtain ⟨b1, b2, b3, b4⟩ := hbox
  have hp1 : 0 ≤ (gz u v z).1 := by
    have : (0 : ℝ) ≤ ((gz u v z).1 : ℝ) := by linarith
    exact_mod_cast this
  have hp2 : 0 ≤ (gz u v z).2 := by
    have : (0 : ℝ) ≤ ((gz u v z).2 : ℝ) := by linarith
    exact_mod_cast this
  set P₁ := (gz u v z).1.toNat
  set P₂ := (gz u v z).2.toNat
  have e1 : ((P₁ : ℕ) : ℤ) = (gz u v z).1 := Int.toNat_of_nonneg hp1
  have e2 : ((P₂ : ℕ) : ℤ) = (gz u v z).2 := Int.toNat_of_nonneg hp2
  have e1r : ((P₁ : ℕ) : ℝ) = ((gz u v z).1 : ℝ) := by exact_mod_cast e1
  have e2r : ((P₂ : ℕ) : ℝ) = ((gz u v z).2 : ℝ) := by exact_mod_cast e2
  have hgcd : Int.gcd z.1 z.2 = 1 := by
    unfold MemParams.zSet at hz
    exact (mem_filter.1 hz).2
  have hcopP : Nat.Coprime P₁ P₂ := by
    have := (gcd_gz_eq_one_iff hu hcop z).2 hgcd
    rw [← e1, ← e2, Int.gcd_natCast_natCast] at this
    exact this
  have hbox' : (P₁, P₂) ∈ posBox U V := by
    simp only [posBox, mem_filter, mem_product, mem_Icc]
    refine ⟨⟨⟨Nat.ceil_le.2 (by rw [e1r]; exact b1), Nat.le_floor (by rw [e1r]; exact b2)⟩,
      Nat.ceil_le.2 (by rw [e2r]; exact b3), Nat.le_floor (by rw [e2r]; exact b4)⟩, hcopP⟩
  have hdvd' : ∀ i k, ℓ i k ∣ P₁ := by
    intro i k
    have := hdvd i k
    rw [physDelta_iff, ← e1] at this
    exact Int.natCast_dvd_natCast.1 this
  refine ⟨⟨((P₁, P₂), ℓ), mem_filter.2 ⟨mem_product.2 ⟨hbox', hℓ⟩, hinj, hdvd'⟩⟩, ?_, rfl⟩
  show ginv u v ((P₁ : ℤ), (P₂ : ℤ)) = z
  rw [e1, e2]
  exact ginv_gz hu hcop z

/-- The unshared (last) labels of a state. -/
def lasts (s : PhysState x a J U V) : Fin K → ℕ := fun i => s.1.2 i (Fin.last J)

lemma newList_apply_last (P : MemParams) (ℓ : P.Lst) (nw : Fin P.K → ℕ) (i : Fin P.K) :
    P.newList ℓ nw i (Fin.last P.J) = nw i := by
  simp [MemParams.newList]

lemma newList_apply_castSucc (P : MemParams) (ℓ : P.Lst) (nw : Fin P.K → ℕ) (i : Fin P.K)
    (k : Fin P.J) : P.newList ℓ nw i k.castSucc = ℓ i k.castSucc := by
  simp [MemParams.newList]

lemma list_eq_newList (t s' : PhysState x a J U V)
    (hpad : ∀ i (k : Fin J), s'.1.2 i k.castSucc = t.1.2 i k.castSucc) :
    s'.1.2 = (pP x a A₀ Y J R d₀ U V B).newList t.1.2 (lasts s') := by
  funext i k
  induction k using Fin.lastCases with
  | last => rw [newList_apply_last]; rfl
  | cast k => rw [newList_apply_castSucc]; exact hpad i k

lemma newList_injective (P : MemParams) (ℓ : P.Lst) (nw : Fin P.K → ℕ) (i : Fin P.K)
    (hinj : Function.Injective (ℓ i)) (hban : nw i ∉ Set.range (ℓ i)) :
    Function.Injective (P.newList ℓ nw i) := by
  intro k k' h
  induction k using Fin.lastCases with
  | last =>
    induction k' using Fin.lastCases with
    | last => rfl
    | cast k' =>
      rw [newList_apply_last, newList_apply_castSucc] at h
      exact absurd ⟨_, h.symm⟩ hban
  | cast k =>
    induction k' using Fin.lastCases with
    | last =>
      rw [newList_apply_last, newList_apply_castSucc] at h
      exact absurd ⟨_, h⟩ hban
    | cast k' =>
      rw [newList_apply_castSucc, newList_apply_castSucc] at h
      exact congrArg _ (Fin.castSucc_injective _ (hinj h))

lemma last_mem_range_swap {M : ℕ} (f g : Fin (M + 1) → ℕ) (hf : Function.Injective f)
    (hfg : ∀ k : Fin M, g k.castSucc = f k.castSucc) :
    f (Fin.last M) ∈ Set.range g → g (Fin.last M) ∈ Set.range f := by
  rintro ⟨k, hk⟩
  induction k using Fin.lastCases with
  | last => exact ⟨Fin.last M, hk.symm⟩
  | cast k =>
    rw [hfg k] at hk
    exact absurd (hf hk) (Fin.castSucc_lt_last k).ne

/-- The cross-edge ban is symmetric for injective lists with common pads. -/
lemma ban_symm (t s' : PhysState x a J U V)
    (hpad : ∀ i (k : Fin J), s'.1.2 i k.castSucc = t.1.2 i k.castSucc) (i : Fin K) :
    s'.1.2 i (Fin.last J) ∉ Set.range (t.1.2 i) ↔ t.1.2 i (Fin.last J) ∉ Set.range (s'.1.2 i) := by
  have ht := (mem_filter.1 t.2).2.1 i
  have hs := (mem_filter.1 s'.2).2.1 i
  constructor
  · exact fun h h' => h (last_mem_range_swap _ _ ht (fun k => hpad i k) h')
  · exact fun h h' => h (last_mem_range_swap _ _ hs (fun k => (hpad i k).symm) h')

lemma padProd_eq_of_pad (t s' : PhysState x a J U V)
    (hpad : ∀ i (k : Fin J), s'.1.2 i k.castSucc = t.1.2 i k.castSucc) :
    padProd s'.1.2 = padProd t.1.2 := by
  unfold padProd; exact prod_congr rfl fun i _ => prod_congr rfl fun k _ => hpad i k

lemma detZ_zOf {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) (t s' : PhysState x a J U V) :
    detZ (zOf u v t) (zOf u v s') = (t.1.1.1 : ℤ) * s'.1.1.2 - (t.1.1.2 : ℤ) * s'.1.1.1 := by
  rw [← detZ_gz hu hcop, gz_zOf hu hcop, gz_zOf hu hcop]; rfl

open Classical in
lemma edgeOK_iff {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)))
    (t s' : PhysState x a J U V)
    (hpad : ∀ i (k : Fin J), s'.1.2 i k.castSucc = t.1.2 i k.castSucc) :
    (pP x a A₀ Y J R d₀ U V B).EdgeOK (rootOf (u, v)) (zOf u v t) (zOf u v s') t.1.2 (lasts s') ↔
      (∀ i, lasts s' i ∉ Set.range (t.1.2 i)) ∧ d₀ ≤ padProd t.1.2 ∧ padProd t.1.2 < 2 * d₀ ∧
        IsGoodRatio x Y a t.1.2 (rootRatio t.1.1.1 t.1.1.2) ∧
        IsGoodRatio x Y a s'.1.2 (rootRatio s'.1.1.1 s'.1.1.2) := by
  have hD := padProd_eq_of_pad t s' hpad
  have hlist := list_eq_newList (A₀ := A₀) (Y := Y) (R := R) (d₀ := d₀) (B := B) t s' hpad
  have hinj := (mem_filter.1 t.2).2.1
  have hboxt := inBox_zOf (A₀ := A₀) (Y := Y) (R := R) (d₀ := d₀) (B := B) hu hcop hU hV t
  have hboxs := inBox_zOf (A₀ := A₀) (Y := Y) (R := R) (d₀ := d₀) (B := B) hu hcop hU hV s'
  have hDdvd : (padProd t.1.2 : ℤ) ∣ detZ (zOf u v t) (zOf u v s') := by
    rw [detZ_zOf hu hcop]
    have h1 := padProd_dvd_pos hdisj t
    have h2 := padProd_dvd_pos hdisj s'
    rw [hD] at h2
    exact dvd_sub (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.2 h1) _)
      (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.2 h2) _)
  have hgt := goodAt_zOf (A₀ := A₀) (Y := Y) (R := R) (d₀ := d₀) (B := B) hu hcop hU hV t t.1.2
  have hgs := goodAt_zOf (A₀ := A₀) (Y := Y) (R := R) (d₀ := d₀) (B := B) hu hcop hU hV s' s'.1.2
  have hgs' : (pP x a A₀ Y J R d₀ U V B).GoodAt (rootOf (u, v)) (zOf u v s')
      ((pP x a A₀ Y J R d₀ U V B).newList t.1.2 (lasts s')) ↔
      IsGoodRatio x Y a s'.1.2 (rootRatio s'.1.1.1 s'.1.1.2) := by rw [← hlist]; exact hgs
  unfold MemParams.EdgeOK
  rw [hgt, hgs']
  constructor
  · rintro ⟨_, hb, hd1, hd2, _, _, _, hg1, hg2⟩
    exact ⟨hb, hd1, hd2, hg1, hg2⟩
  · rintro ⟨hb, hd1, hd2, hg1, hg2⟩
    exact ⟨hinj, hb, hd1, hd2, hDdvd, hboxt, hboxs, hg1, hg2⟩

open Classical in
/-- **The per-term identity of the edge correspondence.** -/
lemma term_eq {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)))
    (j : ℕ) (ψ : (ℤ × ℤ) × (Fin K → Fin (J + 1) → ℕ) → ℂ) (t s' : PhysState x a J U V)
    (hpad : ∀ i (k : Fin J), s'.1.2 i k.castSucc = t.1.2 i k.castSucc) :
    gd Y t * (if Even j then rowOp0 x a A₀ Y J d₀ U V t s'
        else (starRingEnd ℂ) (rowOp0 x a A₀ Y J d₀ U V s' t)) * gd Y s' * ψ (zOf u v s', s'.1.2) =
    (if (pP x a A₀ Y J R d₀ U V B).EdgeOK (rootOf (u, v)) (zOf u v t) (zOf u v s') t.1.2
        (lasts s') then
      ((∏ i, ((pP x a A₀ Y J R d₀ U V B).Vg i)⁻¹ : ℝ) : ℂ) *
        (pP x a A₀ Y J R d₀ U V B).edgeMult j
          (detZ (zOf u v t) (zOf u v s') / padProd t.1.2) (∏ i, lasts s' i) (lastProd t.1.2)
          (padProd t.1.2) *
        ψ (zOf u v s', (pP x a A₀ Y J R d₀ U V B).newList t.1.2 (lasts s'))
    else 0) := by
  have hD := padProd_eq_of_pad t s' hpad
  have hlist := list_eq_newList (A₀ := A₀) (Y := Y) (R := R) (d₀ := d₀) (B := B) t s' hpad
  have hdet := detZ_zOf hu hcop t s'
  have hDdvd : (padProd t.1.2 : ℤ) ∣ detZ (zOf u v t) (zOf u v s') := by
    rw [hdet]
    have h1 := padProd_dvd_pos hdisj t
    have h2 := padProd_dvd_pos hdisj s'
    rw [hD] at h2
    exact dvd_sub (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.2 h1) _)
      (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.2 h2) _)
  rw [edgeOK_iff hu hcop hU hV hdisj t s' hpad, ← hlist]
  have hlastP : (∏ i, lasts s' i) = lastProd s'.1.2 := rfl
  rw [hlastP]
  unfold gd
  by_cases hgt : IsGoodRatio x Y a t.1.2 (rootRatio t.1.1.1 t.1.1.2)
  · by_cases hgs : IsGoodRatio x Y a s'.1.2 (rootRatio s'.1.1.1 s'.1.1.2)
    · rw [if_pos hgt, if_pos hgs]
      by_cases hc : (∀ i, lasts s' i ∉ Set.range (t.1.2 i)) ∧ d₀ ≤ padProd t.1.2 ∧
          padProd t.1.2 < 2 * d₀
      · have hC : ((∀ i, lasts s' i ∉ Set.range (t.1.2 i)) ∧ d₀ ≤ padProd t.1.2 ∧
            padProd t.1.2 < 2 * d₀ ∧ IsGoodRatio x Y a t.1.2 (rootRatio t.1.1.1 t.1.1.2) ∧
            IsGoodRatio x Y a s'.1.2 (rootRatio s'.1.1.1 s'.1.1.2)) :=
          ⟨hc.1, hc.2.1, hc.2.2, hgt, hgs⟩
        rw [if_pos hC]
        unfold MemParams.edgeMult
        by_cases hj : Even j
        · rw [if_pos hj, if_pos hj]
          unfold rowOp0
          rw [if_pos ⟨hpad, hc.1, hc.2.1, hc.2.2⟩, hdet]
          simp only [pP, MemParams.Vg]
          push_cast; ring
        · rw [if_neg hj, if_neg hj]
          unfold rowOp0
          have hc' : (∀ i (k : Fin J), t.1.2 i k.castSucc = s'.1.2 i k.castSucc) ∧
              (∀ i, t.1.2 i (Fin.last J) ∉ Set.range (s'.1.2 i)) ∧
              d₀ ≤ padProd s'.1.2 ∧ padProd s'.1.2 < 2 * d₀ :=
            ⟨fun i k => (hpad i k).symm, fun i => (ban_symm t s' hpad i).1 (hc.1 i),
              hD ▸ hc.2.1, hD ▸ hc.2.2⟩
          rw [if_pos hc']
          have hneg : (((s'.1.1.1 : ℤ) * t.1.1.2 - (s'.1.1.2 : ℤ) * t.1.1.1) / (padProd s'.1.2 : ℤ))
              = -(detZ (zOf u v t) (zOf u v s') / (padProd t.1.2 : ℤ)) := by
            rw [hD, ← Int.neg_ediv_of_dvd hDdvd, hdet]; ring_nf
          rw [hneg, map_mul, Complex.conj_ofReal, hD]
          simp only [pP, MemParams.Vg]
          push_cast; ring
      · have hC : ¬ ((∀ i, lasts s' i ∉ Set.range (t.1.2 i)) ∧ d₀ ≤ padProd t.1.2 ∧
            padProd t.1.2 < 2 * d₀ ∧ IsGoodRatio x Y a t.1.2 (rootRatio t.1.1.1 t.1.1.2) ∧
            IsGoodRatio x Y a s'.1.2 (rootRatio s'.1.1.1 s'.1.1.2)) :=
          fun h => hc ⟨h.1, h.2.1, h.2.2.1⟩
        rw [if_neg hC]
        by_cases hj : Even j
        · rw [if_pos hj]
          unfold rowOp0
          rw [if_neg (fun h => hc ⟨h.2.1, h.2.2⟩)]; simp
        · rw [if_neg hj]
          unfold rowOp0
          rw [if_neg (fun h => hc ⟨fun i => (ban_symm t s' hpad i).2 (h.2.1 i),
            hD ▸ h.2.2.1, hD ▸ h.2.2.2⟩)]
          simp
    · have hC : ¬ ((∀ i, lasts s' i ∉ Set.range (t.1.2 i)) ∧ d₀ ≤ padProd t.1.2 ∧
          padProd t.1.2 < 2 * d₀ ∧ IsGoodRatio x Y a t.1.2 (rootRatio t.1.1.1 t.1.1.2) ∧
          IsGoodRatio x Y a s'.1.2 (rootRatio s'.1.1.1 s'.1.1.2)) := fun h => hgs h.2.2.2.2
      rw [if_neg hgs, if_neg hC]; simp
  · have hC : ¬ ((∀ i, lasts s' i ∉ Set.range (t.1.2 i)) ∧ d₀ ≤ padProd t.1.2 ∧
        padProd t.1.2 < 2 * d₀ ∧ IsGoodRatio x Y a t.1.2 (rootRatio t.1.1.1 t.1.1.2) ∧
        IsGoodRatio x Y a s'.1.2 (rootRatio s'.1.1.1 s'.1.1.2)) := fun h => hgt h.2.2.2.1
    rw [if_neg hgt, if_neg hC]; simp

lemma pad_of_ne (j : ℕ) (t s' : PhysState x a J U V)
    (h : (if Even j then rowOp0 x a A₀ Y J d₀ U V t s'
      else (starRingEnd ℂ) (rowOp0 x a A₀ Y J d₀ U V s' t)) ≠ 0) :
    ∀ i (k : Fin J), s'.1.2 i k.castSucc = t.1.2 i k.castSucc := by
  by_cases hj : Even j
  · rw [if_pos hj] at h
    unfold rowOp0 at h
    by_contra hc
    exact h (if_neg (fun h' => hc h'.1))
  · rw [if_neg hj] at h
    unfold rowOp0 at h
    by_contra hc
    exact h (by rw [if_neg (fun h' => hc fun i k => (h'.1 i k).symm)]; simp)

set_option maxRecDepth 100000 in
open Classical in
/-- **The edge correspondence**: the physical edge sum over targets `s'` at the root `P₀` is the
root edge sum over `(z', new labels)`. -/
lemma edge_corr {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (huU : (u : ℝ) ≤ 16 * U) (hvV : (v : ℝ) ≤ 2 * V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)))
    (j : ℕ) (ψ : (ℤ × ℤ) × (Fin K → Fin (J + 1) → ℕ) → ℂ)
    (hψ : ∀ z (ℓ : Fin K → Fin (J + 1) → ℕ), (∀ i k, ℓ i k ∈ primeGroup x (a i)) →
      (∃ i k, ¬ physDelta (u, v) (ℓ i k) z) → ψ (z, ℓ) = 0)
    (t : PhysState x a J U V) :
    gd Y t * ∑ s' : PhysState x a J U V, (if Even j then rowOp0 x a A₀ Y J d₀ U V t s'
        else (starRingEnd ℂ) (rowOp0 x a A₀ Y J d₀ U V s' t)) * gd Y s' * ψ (zOf u v s', s'.1.2) =
    (pP x a A₀ Y J R d₀ U V B).physEdge (rootOf (u, v)) j ψ (zOf u v t, t.1.2) := by
  set P := pP x a A₀ Y J R d₀ U V B with hP
  set T0 : PhysState x a J U V → ℂ := fun s' => if Even j then rowOp0 x a A₀ Y J d₀ U V t s'
    else (starRingEnd ℂ) (rowOp0 x a A₀ Y J d₀ U V s' t) with hT0
  rw [mul_sum]
  unfold MemParams.physEdge
  rw [← sum_product']
  refine sum_bij_ne_zero (fun s' _ _ => (zOf u v s', lasts s')) ?_ ?_ ?_ ?_
  · intro s' _ _
    refine mem_product.2 ⟨zOf_mem hu hcop hU hV huU hvV s', ?_⟩
    have hc := (mem_product.1 (mem_filter.1 s'.2).1).2
    simp only [listCands, Fintype.mem_piFinset] at hc
    exact Fintype.mem_piFinset.2 fun i => hc i (Fin.last J)
  · intro s₁ _ h₁ s₂ _ h₂ heq
    have hp₁ := pad_of_ne j t s₁ (fun h => h₁ (by rw [h]; simp))
    have hp₂ := pad_of_ne j t s₂ (fun h => h₂ (by rw [h]; simp))
    simp only [Prod.mk.injEq] at heq
    have hpos : s₁.1.1 = s₂.1.1 := by
      have := congrArg (gz u v) heq.1
      rw [gz_zOf hu hcop, gz_zOf hu hcop] at this
      simp only [Prod.mk.injEq, Nat.cast_inj] at this
      exact Prod.ext this.1 this.2
    have hl : s₁.1.2 = s₂.1.2 := by
      rw [list_eq_newList (A₀ := A₀) (Y := Y) (R := R) (d₀ := d₀) (B := B) t s₁ hp₁,
        list_eq_newList (A₀ := A₀) (Y := Y) (R := R) (d₀ := d₀) (B := B) t s₂ hp₂, heq.2]
    exact Subtype.ext (Prod.ext hpos hl)
  · rintro ⟨z', nw⟩ hp hne
    rw [mem_product] at hp
    have hEdge : P.EdgeOK (rootOf (u, v)) (zOf u v t) z' t.1.2 nw := by
      by_contra hc; exact hne (by simp only; rw [if_neg hc])
    have hψne : ψ (z', P.newList t.1.2 nw) ≠ 0 := by
      intro h0; exact hne (by simp only; rw [if_pos hEdge, h0, mul_zero])
    have htc := (mem_product.1 (mem_filter.1 t.2).1).2
    simp only [listCands, Fintype.mem_piFinset] at htc
    have hnw := Fintype.mem_piFinset.1 hp.2
    have hgrp : ∀ i k, P.newList t.1.2 nw i k ∈ primeGroup x (a i) := by
      intro i k
      induction k using Fin.lastCases with
      | last => rw [newList_apply_last]; exact hnw i
      | cast k => rw [newList_apply_castSucc]; exact htc i k.castSucc
    have hdel : ∀ i k, physDelta (u, v) (P.newList t.1.2 nw i k) z' := by
      by_contra hc
      push Not at hc
      exact hψne (hψ z' _ hgrp hc)
    have hinj : ∀ i, Function.Injective (P.newList t.1.2 nw i) := fun i =>
      newList_injective P t.1.2 nw i (hEdge.1 i) (hEdge.2.1 i)
    obtain ⟨s', hz, hl⟩ := exists_state (A₀ := A₀) (Y := Y) (R := R) (d₀ := d₀) (B := B) hu hcop z'
      hp.1 hEdge.2.2.2.2.2.2.1 hU hV (P.newList t.1.2 nw)
      (by simp only [listCands, Fintype.mem_piFinset]; exact hgrp) hinj hdel
    have hlasts : lasts s' = nw := by
      funext i; simp only [lasts, hl]; exact newList_apply_last P _ nw i
    have hpad : ∀ i (k : Fin J), s'.1.2 i k.castSucc = t.1.2 i k.castSucc := by
      intro i k; rw [hl]; exact newList_apply_castSucc P _ nw i k
    have hval := term_eq (A₀ := A₀) (Y := Y) (R := R) (d₀ := d₀) (B := B) hu hcop hU hV hdisj j ψ
      t s' hpad
    refine ⟨s', mem_univ _, ?_, by rw [hz, hlasts]⟩
    intro h0
    apply hne
    simp only
    rw [← hz, ← hlasts, ← hval, ← mul_assoc, ← mul_assoc] at *
    simpa [mul_assoc] using h0
  · intro s' _ hne
    have hpad := pad_of_ne j t s' (fun h => hne (by rw [h]; simp))
    have := term_eq (A₀ := A₀) (Y := Y) (R := R) (d₀ := d₀) (B := B) hu hcop hU hV hdisj j ψ t s' hpad
    simp only [mul_assoc] at this ⊢
    exact this

lemma physEdge_eq_zero_of_not_good (P : MemParams) (ω : ℝ × ℝ × ℝ) (j : ℕ)
    (ψ : (ℤ × ℤ) × P.Lst → ℂ) (z : ℤ × ℤ) (ℓ : P.Lst) (h : ¬ P.GoodAt ω z ℓ) :
    P.physEdge ω j ψ (z, ℓ) = 0 := by
  classical
  unfold MemParams.physEdge
  refine sum_eq_zero fun z' _ => sum_eq_zero fun nw _ => ?_
  rw [if_neg (fun hE => h hE.2.2.2.2.2.2.2.1)]

lemma physEdge_eq_zero_of_not_inj (P : MemParams) (ω : ℝ × ℝ × ℝ) (j : ℕ)
    (ψ : (ℤ × ℤ) × P.Lst → ℂ) (z : ℤ × ℤ) (ℓ : P.Lst) (h : ¬ ∀ i, Function.Injective (ℓ i)) :
    P.physEdge ω j ψ (z, ℓ) = 0 := by
  classical
  unfold MemParams.physEdge
  refine sum_eq_zero fun z' _ => sum_eq_zero fun nw _ => ?_
  rw [if_neg (fun hE => h hE.1)]

lemma goodAt_perm (P : MemParams) (ω : ℝ × ℝ × ℝ) (z : ℤ × ℤ) (ℓ : P.Lst)
    (σ : Fin P.K → Equiv.Perm (Fin (P.J + 1))) :
    P.GoodAt ω z (fun i => ℓ i ∘ σ i) ↔ P.GoodAt ω z ℓ := by
  unfold MemParams.GoodAt; exact isGoodRatio_perm _ _ _ _ _ _

lemma symP_physEdge_eq_zero_of_not_good (P : MemParams) (ω : ℝ × ℝ × ℝ) (j : ℕ)
    (ψ : (ℤ × ℤ) × P.Lst → ℂ) (z : ℤ × ℤ) (ℓ : P.Lst) (h : ¬ P.GoodAt ω z ℓ) :
    P.symP (P.physEdge ω j ψ) (z, ℓ) = 0 := by
  unfold MemParams.symP MemParams.listSym
  rw [sum_eq_zero fun pr _ => physEdge_eq_zero_of_not_good P ω j ψ z _
    (fun h' => h ((goodAt_perm P ω z ℓ pr).1 h')), mul_zero]

lemma symP_physEdge_eq_zero_of_not_inj (P : MemParams) (ω : ℝ × ℝ × ℝ) (j : ℕ)
    (ψ : (ℤ × ℤ) × P.Lst → ℂ) (z : ℤ × ℤ) (ℓ : P.Lst) (h : ¬ ∀ i, Function.Injective (ℓ i)) :
    P.symP (P.physEdge ω j ψ) (z, ℓ) = 0 := by
  unfold MemParams.symP MemParams.listSym
  refine (mul_eq_zero_of_right _ (sum_eq_zero fun pr _ => physEdge_eq_zero_of_not_inj P ω j ψ z _
    (fun h' => h fun i => ?_)))
  have := h' i
  have e : ℓ i = (fun k => ℓ i ∘ pr i) i ∘ (pr i).symm := by
    funext k; simp
  rw [e]; exact this.comp (pr i).symm.injective

lemma gd_permState (s : PhysState x a J U V) (pr : Fin K → Equiv.Perm (Fin (J + 1))) :
    gd Y (permState s pr) = gd Y s := by
  unfold gd permState
  simp only
  by_cases h : IsGoodRatio x Y a s.1.2 (rootRatio s.1.1.1 s.1.1.2)
  · rw [if_pos h, if_pos ((isGoodRatio_perm _ _ _ _ _ _).2 h)]
  · rw [if_neg h, if_neg (fun h' => h ((isGoodRatio_perm _ _ _ _ _ _).1 h'))]

lemma gd_mul_self (s : PhysState x a J U V) : gd Y s * gd Y s = gd Y s := by
  unfold gd; split_ifs <;> simp

lemma halfDamp_permState (s : PhysState x a J U V) (pr : Fin K → Equiv.Perm (Fin (J + 1))) :
    halfDamp (permState s pr) = halfDamp s := rfl

lemma zOf_permState (u v : ℕ) (s : PhysState x a J U V) (pr : Fin K → Equiv.Perm (Fin (J + 1))) :
    zOf u v (permState s pr) = zOf u v s := rfl

lemma physX_mulVec (φ : PhysState x a J U V → ℂ) (s : PhysState x a J U V) :
    (physX x Y a J U V).mulVec φ s = gd Y s * (((((J + 1).factorial ^ K : ℕ) : ℂ))⁻¹ *
      ∑ pr : Fin K → Equiv.Perm (Fin (J + 1)), φ (permState s pr)) := by
  unfold physX
  rw [← Matrix.mulVec_mulVec]
  unfold goodProj
  rw [Matrix.mulVec_diagonal, slotSym_mulVec_eq]
  rfl

lemma avg_const (c : ℂ) :
    ((((J + 1).factorial ^ K : ℕ) : ℂ))⁻¹ * ∑ _pr : Fin K → Equiv.Perm (Fin (J + 1)), c = c := by
  rw [sum_const, card_univ, Fintype.card_pi, prod_const, card_univ, Fintype.card_fin,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  have : (((J + 1).factorial ^ K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
  push_cast at this ⊢
  field_simp

lemma zOf_eq_e1_iff {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) (s : PhysState x a J U V) :
    zOf u v s = (1, 0) ↔ s.1.1 = (u, v) := by
  constructor
  · intro h
    have := congrArg (gz u v) h
    rw [gz_zOf hu hcop, gz_e1] at this
    simp only [Prod.mk.injEq, Nat.cast_inj] at this
    exact Prod.ext this.1 this.2
  · intro h
    unfold zOf; rw [h]; exact ginv_P0 hu hcop

lemma qv_end (P : MemParams) : P.qv P.N = 1 / 2 := by unfold MemParams.qv; simp

lemma qv_zero (P : MemParams) : P.qv 0 = 1 / 2 := by unfold MemParams.qv; simp

lemma qv_mid (P : MemParams) {j : ℕ} (h0 : j ≠ 0) (hN : j ≠ P.N) : P.qv j = 1 / 4 := by
  unfold MemParams.qv; rw [if_neg (by tauto)]

set_option maxRecDepth 100000 in
open Classical in
/-- **The chain correspondence.** -/
theorem chain_corr (hR : 1 ≤ R) {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) (hU : 1 ≤ U)
    (hV : 1 ≤ V) (huU : (u : ℝ) ≤ 16 * U) (hvV : (v : ℝ) ≤ 2 * V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j))) :
    ∀ k ≤ 2 * R, ∀ s : PhysState x a J U V,
      (if k < 2 * R then ((halfDamp s : ℝ) : ℂ) else 1) *
        physV x a A₀ Y J d₀ U V (2 * R) (fun s' => if s'.1.1 = (u, v) then 1 else 0) k s =
      gd Y s * (pP x a A₀ Y J R d₀ U V B).physTail (rootOf (u, v)) (physDelta (u, v)) k
        (fun s'' => if s''.1 = (1, 0) then 1 else 0) (zOf u v s, s.1.2) := by
  set P := pP x a A₀ Y J R d₀ U V B with hP
  have hPN : P.N = 2 * R := rfl
  set ur : (ℤ × ℤ) × P.Lst → ℂ := fun s'' => if s''.1 = (1, 0) then 1 else 0 with hur
  have hurp : ∀ z ℓ (σ : Fin P.K → Equiv.Perm (Fin (P.J + 1))),
      ur (z, fun i => ℓ i ∘ σ i) = ur (z, ℓ) := fun _ _ _ => rfl
  intro k
  induction k with
  | zero =>
    intro _ s
    rw [if_pos (by omega)]
    simp only [physV]
    rw [physX_mulVec]
    have hperm : ∀ pr, (if (permState s pr).1.1 = (u, v) then (1 : ℂ) else 0) =
        if s.1.1 = (u, v) then 1 else 0 := fun pr => rfl
    simp only [hperm, avg_const]
    simp only [MemParams.physTail]
    have hq : P.qv (2 * R) = 1 / 2 := qv_end P
    rw [visitFac_zOf (A₀ := A₀) (Y := Y) (R := R) (d₀ := d₀) (B := B) hu hcop hdisj, hq]
    simp only [hur]
    by_cases hs : s.1.1 = (u, v)
    · rw [if_pos hs, if_pos ((zOf_eq_e1_iff hu hcop s).2 hs)]
      unfold halfDamp; push_cast; ring
    · rw [if_neg hs, if_neg (fun h => hs ((zOf_eq_e1_iff hu hcop s).1 h))]
      ring
  | succ k ih =>
    intro hk s
    have ihk : ∀ s' : PhysState x a J U V, ((halfDamp s' : ℝ) : ℂ) *
        physV x a A₀ Y J d₀ U V (2 * R) (fun s' => if s'.1.1 = (u, v) then 1 else 0) k s' =
        gd Y s' * P.physTail (rootOf (u, v)) (physDelta (u, v)) k ur (zOf u v s', s'.1.2) := by
      intro s'
      have := ih (by omega) s'
      rwa [if_pos (show k < 2 * R by omega)] at this
    have hψ : ∀ z (ℓ : Fin K → Fin (J + 1) → ℕ), (∀ i k, ℓ i k ∈ primeGroup x (a i)) →
        (∃ i k, ¬ physDelta (u, v) (ℓ i k) z) →
        P.physTail (rootOf (u, v)) (physDelta (u, v)) k ur (z, ℓ) = 0 :=
      fun z ℓ hℓ h => physTail_eq_zero P _ _ k ur z ℓ hℓ h
    have hT : ∀ t : PhysState x a J U V, (physT x a A₀ Y J d₀ U V (2 * R - (k + 1))).mulVec
        (physV x a A₀ Y J d₀ U V (2 * R) (fun s' => if s'.1.1 = (u, v) then 1 else 0) k) t =
        ((halfDamp t : ℝ) : ℂ) * ∑ s' : PhysState x a J U V,
          (if Even (2 * R - (k + 1)) then rowOp0 x a A₀ Y J d₀ U V t s'
            else (starRingEnd ℂ) (rowOp0 x a A₀ Y J d₀ U V s' t)) * gd Y s' *
          P.physTail (rootOf (u, v)) (physDelta (u, v)) k ur (zOf u v s', s'.1.2) := by
      intro t
      simp only [Matrix.mulVec, dotProduct, physT_apply]
      rw [mul_sum]
      refine sum_congr rfl fun s' _ => ?_
      rw [mul_assoc _ (gd Y s'), ← ihk s']
      push_cast; ring
    have hE : ∀ pr, gd Y s * (physT x a A₀ Y J d₀ U V (2 * R - (k + 1))).mulVec
        (physV x a A₀ Y J d₀ U V (2 * R) (fun s' => if s'.1.1 = (u, v) then 1 else 0) k)
          (permState s pr) =
        ((halfDamp s : ℝ) : ℂ) * (gd Y s * P.physEdge (rootOf (u, v)) (2 * R - (k + 1))
          (P.physTail (rootOf (u, v)) (physDelta (u, v)) k ur) (zOf u v s, fun i => s.1.2 i ∘ pr i)) := by
      intro pr
      rw [hT, halfDamp_permState]
      have h1 : gd Y s * ∑ s' : PhysState x a J U V,
          (if Even (2 * R - (k + 1)) then rowOp0 x a A₀ Y J d₀ U V (permState s pr) s'
            else (starRingEnd ℂ) (rowOp0 x a A₀ Y J d₀ U V s' (permState s pr))) * gd Y s' *
          P.physTail (rootOf (u, v)) (physDelta (u, v)) k ur (zOf u v s', s'.1.2) =
          P.physEdge (rootOf (u, v)) (2 * R - (k + 1))
            (P.physTail (rootOf (u, v)) (physDelta (u, v)) k ur)
            (zOf u v s, fun i => s.1.2 i ∘ pr i) := by
        have := edge_corr (A₀ := A₀) (Y := Y) (R := R) (d₀ := d₀) (B := B) hu hcop hU hV huU hvV
          hdisj (2 * R - (k + 1)) _ hψ (permState s pr)
        rw [gd_permState, zOf_permState] at this
        exact this
      rw [← h1, ← mul_assoc (gd Y s) (gd Y s), gd_mul_self]
      ring
    have hstep : physV x a A₀ Y J d₀ U V (2 * R) (fun s' => if s'.1.1 = (u, v) then 1 else 0)
        (k + 1) s = ((halfDamp s : ℝ) : ℂ) * (gd Y s * P.symP (P.physEdge (rootOf (u, v))
          (2 * R - (k + 1)) (P.physTail (rootOf (u, v)) (physDelta (u, v)) k ur))
          (zOf u v s, s.1.2)) := by
      simp only [physV]
      rw [physX_mulVec]
      unfold MemParams.symP MemParams.listSym
      rw [mul_left_comm, mul_sum, sum_congr rfl fun pr _ => hE pr, ← mul_sum, ← mul_sum]
      ring
    have hsym : P.symP (P.physTail (rootOf (u, v)) (physDelta (u, v)) k ur) =
        P.physTail (rootOf (u, v)) (physDelta (u, v)) k ur := symP_physTail P _ _ k ur hurp
    have htail : P.physTail (rootOf (u, v)) (physDelta (u, v)) (k + 1) ur (zOf u v s, s.1.2) =
        ((P.qv (2 * R - (k + 1)) ^ excessOmega x a J s.1.1.1 : ℝ) : ℂ) *
        P.symP (P.physEdge (rootOf (u, v)) (2 * R - (k + 1))
          (P.physTail (rootOf (u, v)) (physDelta (u, v)) k ur)) (zOf u v s, s.1.2) := by
      simp only [MemParams.physTail]
      rw [hsym, visitFac_zOf (A₀ := A₀) (Y := Y) (R := R) (d₀ := d₀) (B := B) hu hcop hdisj]
    rw [hstep, htail]
    by_cases hlt : k + 1 < 2 * R
    · rw [if_pos hlt]
      have hq : P.qv (2 * R - (k + 1)) = 1 / 4 :=
        qv_mid P (by omega) (by show 2 * R - (k + 1) ≠ 2 * R; omega)
      rw [hq]
      unfold halfDamp
      have : ((1 / 4 : ℝ) ^ excessOmega x a J s.1.1.1) =
          (1 / 2 : ℝ) ^ excessOmega x a J s.1.1.1 * (1 / 2 : ℝ) ^ excessOmega x a J s.1.1.1 := by
        rw [← mul_pow]; norm_num
      rw [this]; push_cast; ring
    · rw [if_neg hlt]
      have h0 : 2 * R - (k + 1) = 0 := by omega
      rw [h0, qv_zero]
      unfold halfDamp
      push_cast; ring

end Corr

section Final

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {A₀ Y : ℝ} {J R d₀ : ℕ} {U V : ℝ} {B : ℕ}

lemma posBox_facts (hU : 1 ≤ U) (hV : 1 ≤ V) {u v : ℕ} (h : (u, v) ∈ posBox U V) :
    0 < u ∧ Nat.Coprime u v ∧ (u : ℝ) ≤ 16 * U ∧ (v : ℝ) ≤ 2 * V := by
  simp only [posBox, mem_filter, mem_product, mem_Icc] at h
  obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ := h
  refine ⟨?_, h5, ?_, ?_⟩
  · have : 1 ≤ ⌈U⌉₊ := Nat.one_le_ceil_iff.2 (by linarith)
    omega
  · exact (Nat.le_floor_iff (by linarith)).1 h2
  · exact (Nat.le_floor_iff (by linarith)).1 h4

set_option maxRecDepth 100000 in
open Classical in
/-- The per-root identity: the physical chain at `P₀` against `pathPhi`. -/
lemma root_sum (hR : 1 ≤ R) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)))
    {u v : ℕ} (hP₀ : (u, v) ∈ posBox U V) :
    ∑ s : PhysState x a J U V, (if s.1.1 = (u, v) then
      ((opA x a A₀ Y J d₀ U V * (opA x a A₀ Y J d₀ U V)ᴴ) ^ R).mulVec
        (fun s' => if s'.1.1 = (u, v) then 1 else 0) s else 0) =
    ∑ ℓ₀ ∈ listCands x a J, (pP x a A₀ Y J R d₀ U V B).physTail (rootOf (u, v))
      (physDelta (u, v)) (2 * R) (fun s'' => if s''.1 = (1, 0) then 1 else 0) ((1, 0), ℓ₀) := by
  obtain ⟨hu, hcop, huU, hvV⟩ := posBox_facts hU hV hP₀
  set P := pP x a A₀ Y J R d₀ U V B with hP
  set W := P.physTail (rootOf (u, v)) (physDelta (u, v)) (2 * R)
    (fun s'' => if s''.1 = (1, 0) then 1 else 0) with hW
  have hchain : ∀ s : PhysState x a J U V,
      ((opA x a A₀ Y J d₀ U V * (opA x a A₀ Y J d₀ U V)ᴴ) ^ R).mulVec
        (fun s' => if s'.1.1 = (u, v) then 1 else 0) s = gd Y s * W (zOf u v s, s.1.2) := by
    intro s
    rw [mulVec_opA_pow hR]
    have := chain_corr (A₀ := A₀) (Y := Y) (d₀ := d₀) (B := B) hR hu hcop hU hV huU hvV hdisj
      (2 * R) le_rfl s
    rw [if_neg (lt_irrefl _), one_mul] at this
    exact this
  simp only [hchain]
  -- `W (e₁, ℓ)` vanishes unless the source is good
  have hgood : ∀ ℓ : P.Lst, ¬ P.GoodAt (rootOf (u, v)) (1, 0) ℓ → W ((1, 0), ℓ) = 0 := by
    intro ℓ hℓ
    rw [hW]
    have hR' : 2 * R = (2 * R - 1) + 1 := by omega
    rw [hR']
    simp only [MemParams.physTail]
    rw [symP_physEdge_eq_zero_of_not_good P _ _ _ _ _ hℓ, mul_zero]
  have hinj : ∀ ℓ : P.Lst, ¬ (∀ i, Function.Injective (ℓ i)) → W ((1, 0), ℓ) = 0 := by
    intro ℓ hℓ
    rw [hW]
    have hR' : 2 * R = (2 * R - 1) + 1 := by omega
    rw [hR']
    simp only [MemParams.physTail]
    rw [symP_physEdge_eq_zero_of_not_inj P _ _ _ _ _ hℓ, mul_zero]
  have he1 : (1, 0) ∈ P.zSet := by
    have hz : 1000 ≤ P.zMax := by unfold MemParams.zMax; omega
    unfold MemParams.zSet
    simp only [mem_filter, mem_product, mem_Icc]
    refine ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, by decide⟩
  have hbox1 : P.InBox (rootOf (u, v)) (1, 0) := by
    rw [inBox_iff _ hu hcop, gz_e1]
    simp only [posBox, mem_filter, mem_product, mem_Icc] at hP₀
    obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, _⟩ := hP₀
    refine ⟨(Nat.ceil_le.1 h1), ?_, Nat.ceil_le.1 h3, ?_⟩
    · exact_mod_cast (Nat.le_floor_iff (by linarith)).1 h2
    · exact_mod_cast (Nat.le_floor_iff (by linarith)).1 h4
  rw [← sum_filter]
  refine sum_bij_ne_zero (fun s _ _ => s.1.2) ?_ ?_ ?_ ?_
  · intro s _ _
    exact (mem_product.1 (mem_filter.1 s.2).1).2
  · intro s₁ h₁ _ s₂ h₂ _ heq
    simp only [mem_filter, mem_univ, true_and] at h₁ h₂
    exact Subtype.ext (Prod.ext (h₁.trans h₂.symm) heq)
  · intro ℓ hℓ hne
    have hinjℓ : ∀ i, Function.Injective (ℓ i) := by
      by_contra hc; exact hne (hinj ℓ hc)
    have hdel : ∀ i k, physDelta (u, v) (ℓ i k) (1, 0) := by
      by_contra hc
      push Not at hc
      have hg : ∀ i k, ℓ i k ∈ P.grp i := by
        simp only [listCands, Fintype.mem_piFinset] at hℓ; exact hℓ
      exact hne (physTail_eq_zero P _ _ _ _ _ ℓ hg hc)
    obtain ⟨s, hz, hl⟩ := exists_state (A₀ := A₀) (Y := Y) (R := R) (d₀ := d₀) (B := B) hu hcop
      (1, 0) he1 hbox1 hU hV ℓ hℓ hinjℓ hdel
    have hpos : s.1.1 = (u, v) := (zOf_eq_e1_iff hu hcop s).1 hz
    refine ⟨s, mem_filter.2 ⟨mem_univ _, hpos⟩, ?_, hl⟩
    rw [hz, hl]
    intro h0
    apply hne
    have hgd : gd Y s = 1 := by
      by_contra hc
      have : ¬ IsGoodRatio x Y a s.1.2 (rootRatio s.1.1.1 s.1.1.2) := by
        intro h; apply hc; unfold gd; rw [if_pos h]
      have hn : ¬ P.GoodAt (rootOf (u, v)) (1, 0) ℓ := by
        rw [← hz, ← hl]
        exact fun h => this ((goodAt_zOf (A₀ := A₀) (Y := Y) (R := R) (d₀ := d₀) (B := B) hu hcop hU hV
          s s.1.2).1 h)
      exact hne (hgood ℓ hn)
    rw [hgd, one_mul] at h0
    exact h0
  · intro s hs _
    simp only [mem_filter, mem_univ, true_and] at hs
    have hz : zOf u v s = (1, 0) := (zOf_eq_e1_iff hu hcop s).2 hs
    rw [hz]
    unfold gd
    by_cases h : IsGoodRatio x Y a s.1.2 (rootRatio s.1.1.1 s.1.1.2)
    · rw [if_pos h, one_mul]
    · rw [if_neg h, zero_mul]
      refine (hgood s.1.2 fun h' => h ?_).symm
      rw [← hz] at h'
      exact (goodAt_zOf (A₀ := A₀) (Y := Y) (R := R) (d₀ := d₀) (B := B) hu hcop hU hV s s.1.2).1 h'

/-- **D7p, the exact path expansion.** -/
theorem path_expansion : PathExpansionStmt := by
  intro x K a A₀ Y J R d₀ U V B hdisj hR hU hV
  unfold momentSum
  have hfib : ∀ s : PhysState x a J U V, ∑ s' : PhysState x a J U V,
      (if s.1.1 = s'.1.1 then
        ((opA x a A₀ Y J d₀ U V * (opA x a A₀ Y J d₀ U V)ᴴ) ^ R) s s' else 0) =
      ∑ P₀ ∈ posBox U V, (if s.1.1 = P₀ then
        ((opA x a A₀ Y J d₀ U V * (opA x a A₀ Y J d₀ U V)ᴴ) ^ R).mulVec
          (fun s' => if s'.1.1 = P₀ then 1 else 0) s else 0) := by
    intro s
    rw [sum_eq_single_of_mem s.1.1 (mem_posBox_of_state s) fun P₀ _ hne => by rw [if_neg (Ne.symm hne)]]
    rw [if_pos rfl]
    simp only [Matrix.mulVec, dotProduct]
    refine sum_congr rfl fun s' _ => ?_
    split_ifs with h1 h2 h2
    · rw [mul_one]
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rw [mul_zero]
  simp only [hfib]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun P₀ hP₀ => ?_
  obtain ⟨u, v⟩ := P₀
  rw [root_sum (B := B) hR hU hV hdisj hP₀]
  unfold MemParams.pathPhi
  rfl

end Final

end ArtinPrimitiveRoots.L102D
end

section
/-! Check module: `chk_momentSum_eq_sum_pathPhi`, the published statement `momentSum_eq_sum_pathPhi` verbatim, proved from the
development. -/

namespace ArtinPrimitiveRoots

open Finset

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open Finset
theorem solution (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (A₀ Y : ℝ) (J R d₀ : ℕ)
    (U V : ℝ) (B : ℕ)
    (hdisj : ∀ i i', i ≠ i' → Disjoint (primeGroup x (a i)) (primeGroup x (a i')))
    (hR : 1 ≤ R) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    momentSum x a A₀ Y J R d₀ U V =
      ∑ P₀ ∈ posBox U V,
        (⟨x, K, a, A₀, Y, J, 2 * R, d₀, U, V, B⟩ : MemParams).pathPhi (rootOf P₀) (physDelta P₀) :=
  L102D.path_expansion x K a A₀ Y J R d₀ U V B hdisj hR hU hV
end
