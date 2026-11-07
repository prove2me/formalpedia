-- Prove2me | Definitions.Def_BddExp3SUM_Profiles
-- name    : BddExp3SUM_Profiles
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:57:54.777994+00:00
-- url     : https://prove2.me/theorems/929c1f7d-086e-4624-bf78-5f5c30c7b886
-- title:
--   Original-coset counts, profiles, subinstances, and the parameters $h, R, \alpha, \sigma$
-- statement:
--   Let $G=\mathbb Z_M^r$, $\mathcal D=\{d\ge 2:d\mid M\}$, $L=|\mathcal D|$, and for $d\in\mathcal D$ let $H_d=G[d]=\{x:dx=0\}$.
--
--   For a list $S_i\subseteq G$ and $x\in S_i$, $c_{i,d}(x)$ is the number of elements of the **original** list $S_i$ in $x+H_d$, and $s_{i,d}(x)$ is the largest power of two not exceeding $c_{i,d}(x)$. The list is partitioned by the full vector $(s_{i,d}(x))_{d\in\mathcal D}$, and a **subinstance** is a triple $(U_1,U_2,U_3)$ of nonempty profile classes. On it $s_{i,d}$ is constant, and $s_d=\min_i s_{i,d}$.
--
--   The parameters are
--
--   $$h=\lfloor\eta\log_2 n\rfloor,\quad R=2^h,\quad \alpha=\tfrac12-\tfrac\gamma4=\tfrac{1937}{4000},\quad \sigma=\lfloor R^\alpha\rfloor.$$
--
--   The structure `Subinst` records the paper's standing assumptions for a fixed subinstance: $n\ge 16$, $R\ge M$, $|S_i|\le n$, $|S_i|>\sqrt n$.
--
--   **Formalization Note** Counts are never recomputed in $U_i$: the paper's Lemma 2 depends on this. The constant value of $s_{i,d}$ on $U_i$ is read as a supremum over $U_i$.
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Truly Subquadratic 3SUM over Every Bounded-Exponent Abelian Group, STOC 2027 submission (manuscript sha256 19546c9a…), §2, p.2 and (1), p.3

import Mathlib
import Definitions.Def_BddExp3SUM_Instance

namespace BddExp3SUM

/-!
# Original-coset profiles and the parameters `h, R, α, σ`

Zeng, Wang, Cao, Dai, Wang, STOC 2027 submission (manuscript sha256 19546c9a…), §2, p.2 and (1), p.3.

**Formalization Note.**
* `G = Z_M^r` is `Fin r → ZMod M`; lists are `Finset`s (the paper's deduplicated "normalized" lists).
* `c_{i,d}(x)` counts elements of the **original** list `S_i` in `x + H_d`. It is never recounted in
  a profile class `U_i`: the paper stresses this directly below Lemma 2.
* `2 ^ Nat.log 2 c` is the largest power of two not exceeding `c` for `c ≥ 1`; `dyadic` is used only
  at `x ∈ S_i`, where `c ≥ 1`.
* A subinstance has the values `s_{i,d}` constant on `U_i`; `sVal` reads this constant as a supremum
  over `U_i`, which is nonempty.
* `Subinst` collects the paper's standing assumptions on p.2: `n ≥ 16`, `R ≥ M`, `|S_i| ≤ n`,
  `|S_i| > √n`, and that `U` is a triple of nonempty profile classes.
-/

/-- The group `G = Z_M^r`. -/
abbrev Grp (M r : ℕ) := Fin r → ZMod M

/-- `𝒟 = {d ≥ 2 : d ∣ M}`. -/
def Dvs (M : ℕ) : Finset ℕ := (Nat.divisors M).filter fun d => 2 ≤ d

/-- `L = |𝒟|`. -/
def Lcard (M : ℕ) : ℕ := (Dvs M).card

/-- `H_d = G[d] = {x : dx = 0}`. -/
def H (M r d : ℕ) : AddSubgroup (Grp M r) where
  carrier := {x | d • x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change d • a = 0 at ha
    change d • b = 0 at hb
    change d • (a + b) = 0
    rw [smul_add, ha, hb, add_zero]
  neg_mem' := by
    intro a ha
    change d • a = 0 at ha
    change d • (-a) = 0
    rw [smul_neg, ha, neg_zero]

variable {M r : ℕ}

open Classical in
/-- `c_{i,d}(x)`: the number of elements of the original list `S` in `x + H_d`. -/
noncomputable def cosetCount (S : Finset (Grp M r)) (d : ℕ) (x : Grp M r) : ℕ :=
  (S.filter fun y => y - x ∈ H M r d).card

/-- The largest power of two not exceeding `c` (for `c ≥ 1`). -/
def dyadic (c : ℕ) : ℕ := 2 ^ Nat.log 2 c

/-- `s_{i,d}(x)`: the dyadic rounding of the original count. -/
noncomputable def sCount (S : Finset (Grp M r)) (d : ℕ) (x : Grp M r) : ℕ :=
  dyadic (cosetCount S d x)

/-- The full profile vector `(s_{i,d}(x))_{d ∈ 𝒟}`. -/
noncomputable def profile (S : Finset (Grp M r)) (x : Grp M r) : Dvs M → ℕ :=
  fun d => sCount S d x

open Classical in
/-- The number of distinct profiles occurring in `S`. -/
noncomputable def profileCount (S : Finset (Grp M r)) : ℕ := (S.image (profile S)).card

open Classical in
/-- `U` is a triple of nonempty profile classes of the lists `S`: a subinstance. -/
def IsProfileTriple (S U : Fin 3 → Finset (Grp M r)) : Prop :=
  ∀ i, ∃ x ∈ S i, U i = (S i).filter fun y => profile (S i) y = profile (S i) x

/-- `s_{i,d}` on the profile class `U i`, where it is constant. -/
noncomputable def sVal (S U : Fin 3 → Finset (Grp M r)) (i : Fin 3) (d : ℕ) : ℕ :=
  (U i).sup (sCount (S i) d)

/-- `s_d = min_i s_{i,d}`. -/
noncomputable def sMin (S U : Fin 3 → Finset (Grp M r)) (d : ℕ) : ℕ :=
  (Finset.univ : Finset (Fin 3)).inf' Finset.univ_nonempty fun i => sVal S U i d

open Classical in
/-- `T_d`: the number of triples in `U₁ × U₂ × U₃` with sum in `H_d`. -/
noncomputable def countIn (U : Fin 3 → Finset (Grp M r)) (d : ℕ) : ℕ :=
  ((U 0 ×ˢ U 1 ×ˢ U 2).filter fun Q => Q.1 + Q.2.1 + Q.2.2 ∈ H M r d).card

open Classical in
/-- The number of cosets of `H_d` represented in `U`. -/
noncomputable def cosetsRepresented (U : Finset (Grp M r)) (d : ℕ) : ℕ :=
  (U.image fun x => (QuotientAddGroup.mk x : Grp M r ⧸ H M r d)).card

/-- `h = ⌊η log₂ n⌋`. -/
noncomputable def hExp (M n : ℕ) : ℕ := ⌊η M * Real.logb 2 n⌋₊

/-- `R = 2^h`. -/
noncomputable def R (M n : ℕ) : ℕ := 2 ^ hExp M n

/-- `α = 1/2 - γ/4 = 1937/4000`. -/
noncomputable def α : ℝ := 1 / 2 - γ / 4

/-- `σ = ⌊R^α⌋`. -/
noncomputable def σ (M n : ℕ) : ℕ := ⌊(R M n : ℝ) ^ α⌋₊

/-- The standing assumptions of §2, p.2, for a fixed subinstance. -/
structure Subinst (M r n : ℕ) (S U : Fin 3 → Finset (Grp M r)) : Prop where
  two_le : 2 ≤ M
  n_ge : 16 ≤ n
  R_ge : M ≤ R M n
  card_le : ∀ i, (S i).card ≤ n
  sqrt_lt : ∀ i, √(n : ℝ) < (S i).card
  isProfile : IsProfileTriple S U

end BddExp3SUM


