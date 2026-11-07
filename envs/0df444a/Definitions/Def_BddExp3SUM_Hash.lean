-- Prove2me | Definitions.Def_BddExp3SUM_Hash
-- name    : BddExp3SUM_Hash
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:58:49.507195+00:00
-- url     : https://prove2.me/theorems/6f12c7da-26f6-4511-9a11-4856de05abb8
-- title:
--   The certificate (2)–(3), the homomorphisms $\pi, K$, the middle group $B$, and the counts $Z_0, Z_\pi, F$
-- statement:
--   For a subinstance, $\ell$ is the least nonnegative integer with $d^\ell\sigma\ge s_dR$ for all $d\in\mathcal D$, and $e\in\mathcal D$ satisfies $e^\ell<es_eR/\sigma$. For a prime $p\mid e$ put $q=\lfloor\log_pR\rfloor$, $D=p^q$, $k=\ell-q$. The structure `Cert` records this data.
--
--   For rows $u_1,\dots,u_\ell\in\mathbb Z_M^r$ define two homomorphisms
--
--   $$\pi(x)=\bigl(x+H_e,\ (\langle u_j,x\rangle\bmod M)_{j\le k},\ (\langle u_j,x\rangle\bmod (M/p))_{k<j\le\ell}\bigr),$$
--
--   $$K(x)=\bigl(x+H_e,\ (\langle u_j,x\rangle\bmod M)_{j\le\ell}\bigr).$$
--
--   The middle group is $B=\{0\}\times\{0\}^k\times((M/p)\mathbb Z_M)^q$, split as $B_1\times B_2$ with dimensions $\lceil q/2\rceil$, $\lfloor q/2\rfloor$. The counts are: $Z_0$, true zero-sum triples of the subinstance; $Z_\pi$, triples with sum in $\ker\pi$; $F$, triples of nonzero sum in $\ker K$. The **good event** is $F\le 24L\sigma n^2/R$ and $Z_\pi-Z_0\le 24L\sigma n^2$.
--
--   **Formalization Note** Rows are indexed by $k+q$, so $k=\ell-q\ge0$ is built in. The quotient component is taken in $G/H_e$. $B_1$ and $B_2$ are subgroups of the target of $K$, so the paper's $(\mu_1,0)$ and $(0,\mu_2)$ are plain elements. Probabilities over rows are counting ratios.
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Truly Subquadratic 3SUM over Every Bounded-Exponent Abelian Group, STOC 2027 submission (manuscript sha256 19546c9a…), (2)–(6), pp.3–4, and (10), p.4

import Mathlib
import Definitions.Def_BddExp3SUM_Profiles

namespace BddExp3SUM

/-!
# The divisor certificate, the homomorphisms `π, K`, the middle group `B` and the random counts

Zeng, Wang, Cao, Dai, Wang, STOC 2027 submission (manuscript sha256 19546c9a…), (2)–(6), pp.3–4;
`Z₀, Z_π, F` and (10), p.4.

**Formalization Note.**
* The rows are `u : Fin (k + q) → G`, so `ℓ = k + q` and the paper's `k = ℓ - q ≥ 0` is built in; `Cert`
  records that `k + q` is the least row count. Rows `0, …, k-1` are the full ones, the last `q` are
  reduced modulo `M/p`.
* `π` and `K` share the component `x + H_e`, in `G ⧸ H_e`. The paper's residue-vector representation
  of this quotient is not used.
* `B` is a subgroup of the target of `K`. Its splitting `B₁ × B₂` is by the last `q` coordinates:
  `B₁` is the part of `B` vanishing on the last `⌊q/2⌋` of them and `B₂` the part vanishing on the first
  `⌈q/2⌉`, so that the paper's `(μ₁, 0)` and `(0, μ₂)` are simply elements of `B₁`, `B₂`. In Lean,
  `⌈q/2⌉ = (q + 1) / 2`.
* Probabilities and expectations over rows are counting ratios on the finite set of rows.
-/

variable {M r : ℕ}

/-- The row map `x ↦ ⟨u, x⟩` in `Z_M`. -/
def rowHom (u : Grp M r) : Grp M r →+ ZMod M where
  toFun x := ∑ j, u j * x j
  map_zero' := by simp
  map_add' := by
    intro a b
    simp [mul_add, Finset.sum_add_distrib]

/-- The target of `π`. -/
abbrev PiTarget (M r e k q p : ℕ) :=
  (Grp M r ⧸ H M r e) × (Fin k → ZMod M) × (Fin q → ZMod (M / p))

/-- The target of `K`. -/
abbrev KTarget (M r e k q : ℕ) := (Grp M r ⧸ H M r e) × (Fin (k + q) → ZMod M)

/-- Reduction `Z_M → Z_{M/p}`. -/
def reduceHom {p : ℕ} (hp : p ∣ M) : ZMod M →+ ZMod (M / p) :=
  (ZMod.castHom (Nat.div_dvd_of_dvd hp) (ZMod (M / p))).toAddMonoidHom

/-- (4): `π(x) = (x + H_e, (⟨u_j, x⟩ mod M)_{j ≤ k}, (⟨u_j, x⟩ mod (M/p))_{k < j ≤ ℓ})`. -/
def piHash {k q p : ℕ} (hp : p ∣ M) (e : ℕ) (u : Fin (k + q) → Grp M r) :
    Grp M r →+ PiTarget M r e k q p where
  toFun x :=
    ((x : Grp M r ⧸ H M r e),
      (fun j => rowHom (u (Fin.castAdd q j)) x),
      fun j => (reduceHom hp).comp (rowHom (u (Fin.natAdd k j))) x)
  map_zero' := by
    refine Prod.ext rfl (Prod.ext ?_ ?_) <;> funext j <;> simp
  map_add' := by
    intro a b
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · funext j
      exact map_add _ a b
    · funext j
      exact map_add ((reduceHom hp).comp (rowHom (u (Fin.natAdd k j)))) a b

/-- (5): `K(x) = (x + H_e, (⟨u_j, x⟩ mod M)_{j ≤ ℓ})`. -/
def KHash {k q : ℕ} (e : ℕ) (u : Fin (k + q) → Grp M r) :
    Grp M r →+ KTarget M r e k q where
  toFun x := ((x : Grp M r ⧸ H M r e), fun j => rowHom (u j) x)
  map_zero' := by
    refine Prod.ext rfl ?_
    funext j
    simp
  map_add' := by
    intro a b
    refine Prod.ext rfl ?_
    funext j
    simp

/-- (6): `B = {0} × {0}^k × ((M/p) Z_M)^q`. -/
def B (M r e k q p : ℕ) : AddSubgroup (KTarget M r e k q) where
  carrier := {y | y.1 = 0 ∧ (∀ j : Fin k, y.2 (Fin.castAdd q j) = 0) ∧
    ∀ j : Fin q, ∃ a : ZMod M, y.2 (Fin.natAdd k j) = ((M / p : ℕ) : ZMod M) * a}
  zero_mem' := ⟨rfl, fun _ => rfl, fun _ => ⟨0, by simp⟩⟩
  add_mem' := by
    rintro a b ⟨ha₁, ha₂, ha₃⟩ ⟨hb₁, hb₂, hb₃⟩
    refine ⟨by simp [ha₁, hb₁], fun j => by simp [ha₂, hb₂], fun j => ?_⟩
    obtain ⟨c, hc⟩ := ha₃ j
    obtain ⟨d, hd⟩ := hb₃ j
    exact ⟨c + d, by simp [hc, hd, mul_add]⟩
  neg_mem' := by
    rintro a ⟨ha₁, ha₂, ha₃⟩
    refine ⟨by simp [ha₁], fun j => by simp [ha₂], fun j => ?_⟩
    obtain ⟨c, hc⟩ := ha₃ j
    exact ⟨-c, by simp [hc, mul_neg]⟩

/-- `B₁`: the elements of `B` whose last `⌊q/2⌋` coordinates vanish (dimension `⌈q/2⌉`). -/
def B₁ (M r e k q p : ℕ) : AddSubgroup (KTarget M r e k q) :=
  B M r e k q p ⊓
    { carrier := {y | ∀ j : Fin q, (q + 1) / 2 ≤ j.val → y.2 (Fin.natAdd k j) = 0}
      zero_mem' := fun _ _ => rfl
      add_mem' := fun ha hb j hj => by simp [ha j hj, hb j hj]
      neg_mem' := fun ha j hj => by simp [ha j hj] }

/-- `B₂`: the elements of `B` whose first `⌈q/2⌉` of the last `q` coordinates vanish (dimension
`⌊q/2⌋`). -/
def B₂ (M r e k q p : ℕ) : AddSubgroup (KTarget M r e k q) :=
  B M r e k q p ⊓
    { carrier := {y | ∀ j : Fin q, j.val < (q + 1) / 2 → y.2 (Fin.natAdd k j) = 0}
      zero_mem' := fun _ _ => rfl
      add_mem' := fun ha hb j hj => by simp [ha j hj, hb j hj]
      neg_mem' := fun ha j hj => by simp [ha j hj] }

/-- A fixed subinstance with its certificate: the least row count `ℓ = k + q` of (2), a divisor `e`
with (3), a prime `p ∣ e`, and `q = ⌊log_p R⌋`, as on p.3. -/
structure Cert (M r n : ℕ) (S U : Fin 3 → Finset (Grp M r)) (k q e p : ℕ) : Prop
    extends Subinst M r n S U where
  least : IsLeast {ℓ : ℕ | ∀ d ∈ Dvs M, sMin S U d * R M n ≤ d ^ ℓ * σ M n} (k + q)
  e_mem : e ∈ Dvs M
  certificate : (e : ℝ) ^ (k + q) < e * sMin S U e * R M n / σ M n
  p_prime : p.Prime
  p_dvd_e : p ∣ e
  q_eq : q = Nat.log p (R M n)

/-- `p ∣ M` in a certificate. -/
theorem Cert.p_dvd {n k q e p : ℕ} {S U : Fin 3 → Finset (Grp M r)} (h : Cert M r n S U k q e p) :
    p ∣ M :=
  h.p_dvd_e.trans (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp h.e_mem).1)

/-- The probability of an event under the uniform law on a finite set. -/
noncomputable def uniformProb {Ω : Type*} [Fintype Ω] (E : Ω → Prop) : ℝ :=
  open Classical in ((Finset.univ.filter E).card : ℝ) / Fintype.card Ω

/-- The expectation of a real function under the uniform law on a finite set. -/
noncomputable def uniformExp {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / Fintype.card Ω

open Classical in
/-- The number of nonempty classes of a labelling on `U`. -/
noncomputable def classCount {T : Type*} (U : Finset (Grp M r)) (φ : Grp M r → T) : ℕ :=
  (U.image φ).card

open Classical in
/-- `Z₀`: the number of true zero-sum triples in the subinstance. -/
noncomputable def countZero (U : Fin 3 → Finset (Grp M r)) : ℕ :=
  ((U 0 ×ˢ U 1 ×ˢ U 2).filter fun Q => Q.1 + Q.2.1 + Q.2.2 = 0).card

open Classical in
/-- `Z_φ`: the number of triples whose sum is in `ker φ`. -/
noncomputable def countKer {T : Type*} [AddCommGroup T] (U : Fin 3 → Finset (Grp M r))
    (φ : Grp M r →+ T) : ℕ :=
  ((U 0 ×ˢ U 1 ×ˢ U 2).filter fun Q => φ (Q.1 + Q.2.1 + Q.2.2) = 0).card

open Classical in
/-- `F`: the number of triples of nonzero sum in `ker K`. -/
noncomputable def countFalse {T : Type*} [AddCommGroup T] (U : Fin 3 → Finset (Grp M r))
    (K : Grp M r →+ T) : ℕ :=
  ((U 0 ×ˢ U 1 ×ˢ U 2).filter fun Q =>
    Q.1 + Q.2.1 + Q.2.2 ≠ 0 ∧ K (Q.1 + Q.2.1 + Q.2.2) = 0).card

open Classical in
/-- The number of triples whose sum has additive order exactly `d`. -/
noncomputable def countOrder (U : Fin 3 → Finset (Grp M r)) (d : ℕ) : ℕ :=
  ((U 0 ×ˢ U 1 ×ˢ U 2).filter fun Q => addOrderOf (Q.1 + Q.2.1 + Q.2.2) = d).card

/-- The good event (10): `F ≤ 24Lσn²/R` and `Z_π - Z₀ ≤ 24Lσn²`. -/
def GoodEvent {T₁ T₂ : Type*} [AddCommGroup T₁] [AddCommGroup T₂] (n : ℕ)
    (U : Fin 3 → Finset (Grp M r)) (φ : Grp M r →+ T₁) (K : Grp M r →+ T₂) : Prop :=
  (countFalse U K : ℝ) ≤ 24 * Lcard M * σ M n * (n : ℝ) ^ 2 / R M n ∧
    (countKer U φ : ℝ) - countZero U ≤ 24 * Lcard M * σ M n * (n : ℝ) ^ 2

end BddExp3SUM


