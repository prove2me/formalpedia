-- Prove2me | Definitions.Def_IwasawaMainConjecture_algebraic
-- name    : IwasawaMainConjecture_algebraic
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T17:22:18.235734+00:00
-- url     : https://prove2.me/theorems/33979f46-afaf-4ddb-a31f-4e682c3919bb
-- title:
--   Iwasawa module $H_\infty$, $V=H_\infty\otimes\mathbb{Q}_p$, eigenspaces $V_i$ and $h_p(\omega^i,T)$
-- statement:
--   This file sets up the algebraic side of the main conjecture of Iwasawa theory for a prime $p$.
--
--   1. $F_n = \mathbb{Q}(\mu_{p^{n+1}})$ (`F p n`) is the splitting field of $X^{p^{n+1}}-1$ inside a fixed algebraic closure $\overline{\mathbb{Q}}$, and $F_n \subseteq F_{n+1}$.
--   2. $A_n$ (`A p n`) is the $p$-primary part of the ideal class group of $F_n$. By class field theory it is isomorphic to $H_n = \mathrm{Gal}(L_n/F_n)$, where $L_n$ is the $p$-Hilbert class field.
--   3. `normA p n : A_{n+1} → A_n` is the norm map, induced by the relative ideal norm. It corresponds to restriction $H_{n+1} \to H_n$.
--   4. `galA p σ n` is the action of $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $A_n$, $[\mathfrak a] \mapsto [\sigma\mathfrak a]$, through the restriction of $\sigma$ to $F_n$.
--   5. Each finite $p$-group $A_n$ is a $\mathbb{Z}_p$-module, and
--   $$H_\infty = \varprojlim_n A_n$$
--   (`Hinf p`) is the $\mathbb{Z}_p$-module of norm-compatible sequences in $\prod_n A_n$. The group $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ acts on it (`galH p σ`).
--   6. $V = H_\infty \otimes_{\mathbb{Z}_p} \mathbb{Q}_p$ (`V p`) carries the $\mathbb{Q}_p$-linear action `galV p σ`.
--   7. `IsCyclotomicCharValue p σ c` says that $\sigma(\zeta) = \zeta^{c}$ for every $p$-power root of unity $\zeta$ (cyclotomic character $c \in \mathbb{Z}_p$).
--   8. $V_i$ (`eigenspace p i`) is the $\omega^i$-eigenspace of $\Delta = \mathrm{Gal}(F_0/\mathbb{Q})$. It is the set of $v \in V$ with $\sigma v = c^i v$ whenever $\sigma$ has cyclotomic character $c$ satisfying $c^{p-1} = 1$; for such $\sigma$, $\omega(\sigma) = c$.
--   9. For $\gamma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$,
--   $$h_p(\omega^i, T) = \det\big(T - (\gamma - 1) \mid V_i\big) \in \mathbb{Q}_p[T]$$
--   (`charPoly p i γ`). This is the characteristic polynomial of $\gamma$ on $V_i$, written in the Iwasawa variable $T = \gamma - 1$.
--
--   These are the objects $F_n$, $H_n$, $H_\infty$, $V$, $V_i$ and $h_p(\omega^i,T)$ of the source's statement.
--
--   **Formalization Note** The action of $\sigma$ on $H_\infty$ is the restriction of the componentwise action on $\prod_n A_n$, and $\gamma-1$ on $V_i$ is the restriction of $\gamma - 1$ on $V$. Both use `if h : (stable) then restrict else 0`: the stability facts hold because the Galois action commutes with norms and $\mathrm{Gal}(F_\infty/\mathbb{Q})$ is abelian, but they are not proved in this file. Likewise `charPoly` is $0$ if $V_i$ were infinite-dimensional; it is in fact finite-dimensional.
-- source:
--   Wikipedia, "Main conjecture of Iwasawa theory", revision oldid=1367440598, https://en.wikipedia.org/w/index.php?title=Main_conjecture_of_Iwasawa_theory&oldid=1367440598, section "Statement" (definitions of F_n, H_n, H_∞, V, ω, V_i, h_p, u); Mazur–Wiles 1984, https://doi.org/10.1007/BF01388599

import Mathlib

/-!
# Iwasawa main conjecture — algebraic side
-/

open scoped nonZeroDivisors NumberField Polynomial TensorProduct

namespace IwasawaMainConjecture

section ClassGroupMap

variable {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]

/-- A multiplicative map on ideals that reflects `⊥` maps nonzero ideals to nonzero ideals. -/
noncomputable def nzIdealMap (f : Ideal S →*₀ Ideal R) (hf : ∀ I, f I = ⊥ → I = ⊥) :
    (Ideal S)⁰ →* (Ideal R)⁰ where
  toFun I := ⟨f I, mem_nonZeroDivisors_of_ne_zero fun h =>
    nonZeroDivisors.coe_ne_zero I (hf _ h)⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' I J := Subtype.ext (map_mul f (I : Ideal S) J)

theorem mk0_nzIdealMap_eq (f : Ideal S →*₀ Ideal R) (hf : ∀ I, f I = ⊥ → I = ⊥)
    (hprin : ∀ x : S, (f (Ideal.span {x})).IsPrincipal) {I J : (Ideal S)⁰}
    (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    ClassGroup.mk0 (nzIdealMap f hf I) = ClassGroup.mk0 (nzIdealMap f hf J) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp h
  have key := congrArg f hxy
  rw [map_mul, map_mul] at key
  obtain ⟨a, ha⟩ := (hprin x).principal
  obtain ⟨b, hb⟩ := (hprin y).principal
  rw [ClassGroup.mk0_eq_mk0_iff]
  refine ⟨a, b, ?_, ?_, ?_⟩
  · rintro rfl
    apply hx
    have : f (Ideal.span {x}) = ⊥ := by rw [ha]; simp
    simpa using hf _ this
  · rintro rfl
    apply hy
    have : f (Ideal.span {y}) = ⊥ := by rw [hb]; simp
    simpa using hf _ this
  · change Ideal.span {a} * f I = Ideal.span {b} * f J
    rw [← Ideal.submodule_span_eq, ← Ideal.submodule_span_eq, ← ha, ← hb]
    exact key

/-- The homomorphism of class groups induced by a multiplicative map on ideals which
reflects `⊥` and sends principal ideals to principal ideals. -/
noncomputable def classGroupMap (f : Ideal S →*₀ Ideal R) (hf : ∀ I, f I = ⊥ → I = ⊥)
    (hprin : ∀ x : S, (f (Ideal.span {x})).IsPrincipal) : ClassGroup S →* ClassGroup R where
  toFun c := ClassGroup.mk0 (nzIdealMap f hf (Classical.choose (ClassGroup.mk0_surjective c)))
  map_one' := by
    refine (mk0_nzIdealMap_eq f hf hprin (J := 1)
      ((Classical.choose_spec (ClassGroup.mk0_surjective (1 : ClassGroup S))).trans
        (map_one _).symm)).trans ?_
    rw [map_one, map_one]
  map_mul' c d := by
    rw [← map_mul ClassGroup.mk0, ← map_mul (nzIdealMap f hf)]
    apply mk0_nzIdealMap_eq f hf hprin
    rw [map_mul, Classical.choose_spec (ClassGroup.mk0_surjective (c * d)),
      Classical.choose_spec (ClassGroup.mk0_surjective c),
      Classical.choose_spec (ClassGroup.mk0_surjective d)]

end ClassGroupMap

section Tower

variable (p : ℕ) [Fact p.Prime]

/-- `F p n = ℚ(μ_{p^{n+1}})`, the splitting field of `X^{p^{n+1}} - 1` inside a fixed
algebraic closure of `ℚ`. -/
noncomputable def F (n : ℕ) : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.adjoin ℚ
    ((Polynomial.X ^ (p ^ (n + 1)) - 1 : ℚ[X]).rootSet (AlgebraicClosure ℚ))

instance (n : ℕ) : Polynomial.IsSplittingField ℚ (F p n)
    (Polynomial.X ^ (p ^ (n + 1)) - 1 : ℚ[X]) :=
  IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)

instance (n : ℕ) : FiniteDimensional ℚ (F p n) :=
  Polynomial.IsSplittingField.finiteDimensional _ (Polynomial.X ^ (p ^ (n + 1)) - 1 : ℚ[X])

instance (n : ℕ) : NumberField (F p n) := ⟨⟩

instance (n : ℕ) : Normal ℚ (F p n) :=
  Normal.of_isSplittingField (Polynomial.X ^ (p ^ (n + 1)) - 1 : ℚ[X])

theorem F_le_succ (n : ℕ) : F p n ≤ F p (n + 1) := by
  rw [F, IntermediateField.adjoin_le_iff]
  intro x hx
  apply IntermediateField.subset_adjoin
  have hne : ∀ m : ℕ, 0 < m → (Polynomial.X ^ m - 1 : ℚ[X]) ≠ 0 := fun m hm => by
    simpa using Polynomial.X_pow_sub_C_ne_zero hm (1 : ℚ)
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  rw [Polynomial.mem_rootSet] at hx ⊢
  refine ⟨hne _ (by positivity), ?_⟩
  have h1 : x ^ (p ^ (n + 1)) = 1 := by simpa [sub_eq_zero] using hx.2
  simp [pow_succ p (n + 1), pow_mul, h1]

end Tower

section NormGalois

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- The norm map `Cl(𝓞 L) → Cl(𝓞 K)` on ideal class groups, induced by the relative ideal
norm `Ideal.relNorm`. -/
noncomputable def classGroupNorm : ClassGroup (𝓞 L) →* ClassGroup (𝓞 K) :=
  classGroupMap (Ideal.relNorm (𝓞 K)) (fun _ h => Ideal.relNorm_eq_bot_iff.mp h)
    (fun x => ⟨⟨_, Ideal.relNorm_singleton (𝓞 K) x⟩⟩)

variable {L} in
/-- The automorphism of `Cl(𝓞 L)` induced by a field automorphism `σ` of `L`
(`[𝔞] ↦ [σ 𝔞]`). -/
noncomputable def classGroupGalois (σ : L ≃+* L) : ClassGroup (𝓞 L) →* ClassGroup (𝓞 L) :=
  classGroupMap (Ideal.mapHom (NumberField.RingOfIntegers.mapRingEquiv σ)).toMonoidWithZeroHom
    (fun _ h => (Ideal.map_eq_bot_iff_of_injective
      (NumberField.RingOfIntegers.mapRingEquiv σ).injective).mp h)
    (fun x => ⟨⟨NumberField.RingOfIntegers.mapRingEquiv σ x, by
      simp [Ideal.map_span, Set.image_singleton]⟩⟩)

end NormGalois

/-- A group homomorphism maps `p`-primary components into `p`-primary components. -/
def primaryMap {G H : Type*} [CommGroup G] [CommGroup H] (p : ℕ) (f : G →* H) :
    CommGroup.primaryComponent G p →* CommGroup.primaryComponent H p :=
  (f.comp (CommGroup.primaryComponent G p).subtype).codRestrict _ fun x => by
    obtain ⟨k, hk⟩ := x.2
    exact ⟨k, by simp [← map_pow, hk]⟩

section Levels

variable (p : ℕ) [Fact p.Prime]

/-- `A p n` is the `p`-primary part of the ideal class group of `F p n = ℚ(μ_{p^{n+1}})`.
By class field theory it is isomorphic to `H_n = Gal(L_n / F_n)`, where `L_n` is the
`p`-Hilbert class field of `F_n`. -/
noncomputable abbrev A (n : ℕ) : Subgroup (ClassGroup (𝓞 (F p n))) :=
  CommGroup.primaryComponent (ClassGroup (𝓞 (F p n))) p

/-- The norm map `A p (n+1) → A p n` (corresponding to restriction
`Gal(L_{n+1}/F_{n+1}) → Gal(L_n/F_n)` under class field theory). -/
noncomputable def normA (n : ℕ) : A p (n + 1) →* A p n :=
  letI : Algebra (F p n) (F p (n + 1)) := (IntermediateField.inclusion (F_le_succ p n)).toAlgebra
  primaryMap p (classGroupNorm (F p n) (F p (n + 1)))

/-- The action of an automorphism `σ` of `ℚ̄` on `A p n`, through its restriction to the
normal field `F p n`. -/
noncomputable def galA (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (n : ℕ) :
    A p n →* A p n :=
  primaryMap p (classGroupGalois (σ.restrictNormal (F p n)).toRingEquiv)

/-- The exponent used to view `A p n` as a `ℤ/p^e`-module. -/
noncomputable def expo (n : ℕ) : ℕ := Nat.card (A p n)

theorem pow_expo_nsmul_eq_zero (n : ℕ) (x : Additive (A p n)) :
    (p ^ expo p n) • x = 0 := by
  have hp : p.Prime := Fact.out
  set g : A p n := Additive.toMul x
  obtain ⟨j, hj⟩ := (CommGroup.mem_primaryComponent_iff_orderOf (p := p)).mp g.2
  have hg : orderOf g = p ^ j := by rw [← hj, Subgroup.orderOf_coe]
  have hdvd : p ^ j ∣ expo p n := hg ▸ orderOf_dvd_natCard g
  have hpos : 0 < expo p n := Nat.card_pos
  have hle : j ≤ expo p n :=
    le_trans (Nat.lt_pow_self hp.one_lt).le (Nat.le_of_dvd hpos hdvd)
  have : g ^ (p ^ expo p n) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (hg ▸ pow_dvd_pow p hle)
  change Additive.ofMul (g ^ (p ^ expo p n)) = 0
  rw [this]; rfl

noncomputable instance (n : ℕ) : Module ℤ_[p] (Additive (A p n)) :=
  letI := AddCommGroup.zmodModule (pow_expo_nsmul_eq_zero p n)
  Module.compHom _ (PadicInt.toZModPow (p := p) (expo p n))

theorem smul_def (n : ℕ) (a : ℤ_[p]) (x : Additive (A p n)) :
    a • x = (PadicInt.toZModPow (p := p) (expo p n) a).val • x := by
  let := AddCommGroup.zmodModule (pow_expo_nsmul_eq_zero p n)
  have : NeZero (p ^ expo p n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  change (PadicInt.toZModPow (p := p) (expo p n) a) • x = _
  conv_lhs => rw [← ZMod.natCast_zmod_val (PadicInt.toZModPow (p := p) (expo p n) a)]
  exact Nat.cast_smul_eq_nsmul (ZMod (p ^ expo p n)) _ x

theorem map_smul_of_addMonoidHom {n m : ℕ} (f : Additive (A p n) →+ Additive (A p m))
    (a : ℤ_[p]) (x : Additive (A p n)) : f (a • x) = a • f x := by
  have hp : p.Prime := Fact.out
  rw [smul_def, smul_def, map_nsmul]
  set k := min (expo p n) (expo p m)
  have hy : p ^ k • f x = 0 := by
    rcases le_total (expo p n) (expo p m) with h | h
    · rw [show k = expo p n from min_eq_left h, ← map_nsmul, pow_expo_nsmul_eq_zero, map_zero]
    · rw [show k = expo p m from min_eq_right h, pow_expo_nsmul_eq_zero]
  have hmod : ∀ v : ℕ, v • f x = (v % p ^ k) • f x := fun v => by
    conv_lhs => rw [← Nat.mod_add_div v (p ^ k)]
    rw [add_nsmul, mul_nsmul, hy, nsmul_zero, add_zero]
  have hv : ∀ e, k ≤ e → (PadicInt.toZModPow (p := p) e a).val % p ^ k =
      ((PadicInt.toZModPow (p := p) k a).val) := fun e he => by
    rw [← PadicInt.cast_toZModPow k e he a, ZMod.cast_eq_val, ZMod.val_natCast]
  rw [hmod, hmod (PadicInt.toZModPow (p := p) (expo p m) a).val, hv _ (min_le_left _ _),
    hv _ (min_le_right _ _)]

/-- An additive homomorphism between two levels is automatically `ℤ_p`-linear. -/
noncomputable def toLinear {n m : ℕ} (f : Additive (A p n) →+ Additive (A p m)) :
    Additive (A p n) →ₗ[ℤ_[p]] Additive (A p m) :=
  { f with map_smul' := map_smul_of_addMonoidHom p f }

end Levels

section InverseLimit

variable (p : ℕ) [Fact p.Prime]

/-- `H∞ = lim← A_n`, the inverse limit of the `p`-parts of the class groups of `F_n` along the
norm maps, realised as the `ℤ_p`-submodule of norm-compatible sequences in `∏ₙ A_n`. -/
noncomputable def Hinf : Submodule ℤ_[p] (∀ n, Additive (A p n)) where
  carrier := {x | ∀ n, (normA p n).toAdditive (x (n + 1)) = x n}
  zero_mem' n := by simp
  add_mem' {x y} hx hy n := by
    change (normA p n).toAdditive (x (n + 1) + y (n + 1)) = x n + y n
    rw [map_add, hx n, hy n]
  smul_mem' a x hx n := by
    change (normA p n).toAdditive (a • x (n + 1)) = a • x n
    rw [map_smul_of_addMonoidHom, hx n]

/-- Componentwise action of `σ ∈ Gal(ℚ̄/ℚ)` on `∏ₙ A_n`. -/
noncomputable def galProd (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (∀ n, Additive (A p n)) →ₗ[ℤ_[p]] (∀ n, Additive (A p n)) :=
  LinearMap.pi fun n => (toLinear p (galA p σ n).toAdditive).comp (LinearMap.proj n)

open Classical in
/-- The action of `σ ∈ Gal(ℚ̄/ℚ)` on `H∞`: the restriction of the componentwise action
(which preserves `H∞`, since the Galois action commutes with the norm maps). -/
noncomputable def galH (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Hinf p →ₗ[ℤ_[p]] Hinf p :=
  if h : ∀ x ∈ Hinf p, galProd p σ x ∈ Hinf p then (galProd p σ).restrict h else 0

/-- `V = H∞ ⊗_{ℤ_p} ℚ_p` (written as `ℚ_p ⊗_{ℤ_p} H∞`, a `ℚ_p`-vector space). -/
abbrev V : Type _ := ℚ_[p] ⊗[ℤ_[p]] Hinf p

/-- The `ℚ_p`-linear action of `σ ∈ Gal(ℚ̄/ℚ)` on `V`. -/
noncomputable def galV (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : V p →ₗ[ℚ_[p]] V p :=
  LinearMap.baseChange ℚ_[p] (galH p σ)

/-- `c ∈ ℤ_p` is the value of the `p`-adic cyclotomic character at `σ`: `σ ζ = ζ ^ c` for every
`p`-power root of unity `ζ ∈ ℚ̄` (where `ζ ^ c := ζ ^ (c mod p^k)` if `ζ ^ (p^k) = 1`). -/
def IsCyclotomicCharValue (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℤ_[p]) : Prop :=
  ∀ (k : ℕ) (ζ : AlgebraicClosure ℚ), ζ ^ (p ^ k) = 1 → σ ζ = ζ ^ (PadicInt.toZModPow k c).val

/-- `V_i`, the `ω^i`-eigenspace of `V` for `Δ = Gal(F_0/ℚ)`: the elements `σ ∈ Gal(ℚ̄/ℚ)`
lying over `Δ ⊂ Gal(F_∞/ℚ)` are those whose cyclotomic character `c` is a `(p-1)`-st root of
unity, and then `ω(σ) = c`. -/
noncomputable def eigenspace (i : ℤ) : Submodule ℚ_[p] (V p) :=
  ⨅ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℤ_[p])
    (_ : IsCyclotomicCharValue p σ c) (_ : c ^ (p - 1) = 1),
    LinearMap.ker (galV p σ - ((c : ℚ_[p]) ^ i) • LinearMap.id)

/-- The operator `γ - 1` on `V`, for `γ ∈ Gal(ℚ̄/ℚ)`. -/
noncomputable def gammaSubOne (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    V p →ₗ[ℚ_[p]] V p :=
  galV p γ - LinearMap.id

open Classical in
/-- `γ - 1` restricted to `V_i` (which it preserves, as `Gal(F_∞/ℚ)` is abelian). -/
noncomputable def gammaSubOneEig (i : ℤ) (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    eigenspace p i →ₗ[ℚ_[p]] eigenspace p i :=
  if h : ∀ v ∈ eigenspace p i, gammaSubOne p γ v ∈ eigenspace p i then
    (gammaSubOne p γ).restrict h else 0

open Classical in
/-- `h_p(ω^i, T) = det(T - (γ - 1) | V_i) ∈ ℚ_p[T]`: the characteristic polynomial of `γ`
acting on `V_i`, written in the Iwasawa variable `T = γ - 1` (equivalently, the
characteristic polynomial of the operator `γ - 1` on `V_i`). It is defined to be `0` if
`V_i` were infinite-dimensional. -/
noncomputable def charPoly (i : ℤ) (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ℚ_[p][X] :=
  if h : FiniteDimensional ℚ_[p] (eigenspace p i) then
    haveI := h
    haveI : Module.Free ℚ_[p] (eigenspace p i) := Module.Free.of_divisionRing _ _
    (gammaSubOneEig p i γ).charpoly
  else 0

end InverseLimit

end IwasawaMainConjecture


