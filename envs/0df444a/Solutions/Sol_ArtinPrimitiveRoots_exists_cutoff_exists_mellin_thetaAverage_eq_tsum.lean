-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_exists_mellin_thetaAverage_eq_tsum
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:10:19.68655+00:00
-- url     : https://prove2.me/submissions/6164b5d7-fe9d-41ee-ac30-935ed865da6a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Theorems.Thm_NumberField_natCard_sUnit_quotient_range_powMonoidHom
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_exists_mellin_thetaAverage_eq_tsum_localWhittaker
import Mathlib

section
section
/-! # L3V_LocStmt: the local statement `L3V_LocPkg` (Lemma 6.2 and the local symbols at one prime)

At an exterior prime `P` (for `𝔪` divisible by the small primes): the sextic symbol is
multiplicative with sixth power `1` on units; `R ∖ P R` is the valuation-`1` part of `R`;
`v_P(gen I) = v_P(I)`; `χ_P` on `P`-units of `F` is multiplicative, of order dividing `6`, and extends
`χ_P` on `R`; and Lemma 6.2: the masked digit sum splits off the zero digit, `α_{P,j}(0) = 0` for
`j ≠ 0`, the nonzero digits give `R(t) = R(1) χ_P(t)^{b(j,e)}` ((6.15), `b(j,0) = 8 + 5j ≡ 8 − j`,
`b(j,e) = 4 + 2e`), `R = 0` for `j = 1`, `e > 0` ((6.14)), `|R(1)| ≤ β_P(e)` ((6.20)), `|α(0)| ≤ 1`
and `|γ₂(P)| ≤ 1`. -/

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

open Classical in
/-- The local statement (see the module doc). -/
def L3V_LocPkg (n : ℕ) (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (g : AllowedGen ι 𝔪),
    let lsym : Ideal (𝓞 F) → F → ℂ := fun P t =>
      if h : ∃ yz : SInt 𝔪 × SInt 𝔪, yz.2 ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
          (yz.2 : F) * t = (yz.1 : F) then
        sexticResidueSymbol ι 𝔪 P h.choose.1 * starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P h.choose.2)
      else 0
    let ladd : Ideal (𝓞 F) → F → ℂ := fun P w =>
      if h : ∃ yzr : SInt 𝔪 × SInt 𝔪 × SInt 𝔪, yzr.2.1 ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
          yzr.2.2 ∈ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
          (yzr.2.1 : F) * (w - (yzr.1 : F)) = (yzr.2.2 : F) then
        sAddChar 𝔪 (-((h.choose.1 : F) / (g.gen P : F)))
      else 0
    let Wv : Ideal (𝓞 F) → ℕ → ℂ := fun P e =>
      if e % 3 = 0 then (((Ideal.absNorm P : ℝ) ^ (-((e / 3 : ℕ) : ℝ)) : ℝ) : ℂ)
      else if e % 3 = 1 then
        (((Ideal.absNorm P : ℝ) ^ (-((e / 3 : ℕ) : ℝ) - 1 / 2) : ℝ) : ℂ) * gaussPhase g 2 P
      else 0
    let Wsph : Ideal (𝓞 F) → ℤ → F → ℂ := fun P e₀ t =>
      if e₀ < 0 then 0 else lsym P t ^ (2 * e₀.toNat) * Wv P e₀.toNat
    let tau : Ideal (𝓞 F) → ℕ → ℂ := fun P j =>
      ∑ᶠ v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)),
        starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P (quotLift v)) ^ j *
          sAddChar 𝔪 (-((quotLift v : F) / (g.gen P : F)))
    let mask : (P : Ideal (𝓞 F)) → ℕ → (SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪))) → ℂ :=
      fun P j v =>
        if j = 0 then (if v = 0 then 1 - (Ideal.absNorm P : ℂ)⁻¹ else -(Ideal.absNorm P : ℂ)⁻¹)
        else (tau P j)⁻¹ * starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P (quotLift v)) ^ j
    let Wweyl : (P : Ideal (𝓞 F)) → ℤ → F → (SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪))) → ℂ :=
      fun P e₀ t v =>
        if e₀ + 2 < 0 then 0 else
          Wv P (e₀ + 2).toNat * lsym P t ^ (4 + 2 * (e₀ + 2).toNat) *
            sexticResidueSymbol ι 𝔪 P (quotLift v) ^ 4 *
            ladd P ((g.gen P : F) ^ (e₀ + 2).toNat * t / (quotLift v : F))
    let Eloc : Ideal (𝓞 F) → ℕ → ℤ → F → ℂ := fun P k e₀ t =>
      if k = 0 then Wsph P e₀ t else
        ∑ᶠ v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)),
          mask P (k % 6) v * (if v = 0 then Wsph P e₀ t else Wweyl P e₀ t v)
    let Rsum : (P : Ideal (𝓞 F)) → ℕ → ℤ → F → ℂ := fun P j e₀ t =>
      ∑ᶠ v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)),
        mask P j v * (if v = 0 then 0 else Wweyl P e₀ t v)
    let βp : ℝ → ℕ → ℝ := fun q e =>
      if e = 0 then 1
      else if e % 3 = 1 then q ^ (-((e / 3 : ℕ) : ℝ))
      else if e % 3 = 0 then q ^ ((1 : ℝ) / 2 - ((e / 3 : ℕ) : ℝ))
      else 0
    ∀ (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hPe : IsExterior 𝔪 P),
      let val := (⟨P, hP, hPe.1⟩ : IsDedekindDomain.HeightOneSpectrum (𝓞 F)).valuation F
      (∀ x y : SInt 𝔪, sexticResidueSymbol ι 𝔪 P (x * y) =
        sexticResidueSymbol ι 𝔪 P x * sexticResidueSymbol ι 𝔪 P y) ∧
      (∀ x : SInt 𝔪, x ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) → sexticResidueSymbol ι 𝔪 P x ^ 6 = 1) ∧
      (∀ y : SInt 𝔪, y ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ↔ val (y : F) = 1) ∧
      (∀ I : Ideal (𝓞 F), IsExterior 𝔪 I →
        val (g.gen I : F) = WithZero.exp (-(((normalizedFactors I).count P : ℕ) : ℤ))) ∧
      (∀ t t' : F, val t = 1 → val t' = 1 → lsym P (t * t') = lsym P t * lsym P t') ∧
      (∀ t : F, val t = 1 → lsym P t ^ 6 = 1) ∧
      (∀ y : SInt 𝔪, y ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) →
        lsym P (y : F) = sexticResidueSymbol ι 𝔪 P y) ∧
      (∀ k : ℕ, k ≠ 0 → ∀ (e₀ : ℤ) (t : F),
        Eloc P k e₀ t = mask P (k % 6) 0 * Wsph P e₀ t + Rsum P (k % 6) e₀ t) ∧
      (∀ j : ℕ, j ≠ 0 → mask P j 0 = 0) ∧
      (∀ j : ℕ, j < 6 → ∀ e₀ : ℤ, 0 ≤ e₀ + 2 → ∀ t : F, val t = 1 →
        Rsum P j e₀ t = Rsum P j e₀ 1 *
          lsym P t ^ (if (e₀ + 2).toNat = 0 then 8 + 5 * j else 4 + 2 * (e₀ + 2).toNat)) ∧
      (∀ e₀ : ℤ, 0 < e₀ + 2 → ∀ t : F, val t ≤ 1 → Rsum P 1 e₀ t = 0) ∧
      (∀ j : ℕ, j < 6 → ∀ e₀ : ℤ, 0 ≤ e₀ + 2 →
        ‖Rsum P j e₀ 1‖ ≤ βp (Ideal.absNorm P) (e₀ + 2).toNat) ∧
      (∀ j : ℕ, ‖mask P j 0‖ ≤ 1) ∧
      ‖gaussPhase g 2 P‖ ≤ 1

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3V_Cut: the candidate cut `L3V_CutKP` (the integrated cubic-theta functional equation)

For a row `r = (𝔟, υ)` and `l > 0`, the forward theta average `T_m(l)` (Lemma 6.1, first formula,
`eq:reflection-unreflected`; Cut63V's left side verbatim) equals the reflected expansion of
`eq:reflection-theta-average` *before* any digit sum is evaluated: the sum over the nonconstant
rational frequencies `ν ∈ F^× / U_S^6` of
* the exterior local Whittaker product `∏_P E_P(ν)`, with
  - `E_P(ν) = W_P(a(ν))` (5.4) for `P ∤ 𝔟`;
  - `E_P(ν) = ∑_{v mod P} α_{P,j}(v) W_P(a(ν) w n(v/p))` for `P ∣ 𝔟`, `j = v_P(𝔟) mod 6`, with the
    masks (6.4) and, for `v ≠ 0`, `W_P(a(p^{e−2}t) w n(v/p)) = W_e χ(t)^{4+2e} χ(v)^4 ψ_P(p^{e−1}t/v)`
    (the per-digit value in the proof of Lemma 6.2), `W_P(a(ν))` for `v = 0`;
* the separated `S`-character `L_υ(ν)^{-1}` and the sheet profile `H_{υ,[ν]}(|ν|_S / l)` of
  `eq:reflection-S-unfolding`/`eq:reflection-profiles`.
Here `lsym P t = χ_P(t)` for a `P`-unit `t ∈ F` (`0` otherwise) and `ladd P w = ψ_P(w/p)` for
`P`-integral `w` (`ψ_P(y/p) = e(−y/p)` for `y ∈ R`), both through a chosen representation by
elements of `R`. Every such `ν` with a nonzero exterior product has `ν b² ∈ R` (`b = gen 𝔟`), so the frequencies are
written `ν = x / b²` with `x` running over `RowClass 𝔪 ≅ (R ∖ 0)/U_S^6`; and `E_P = 1` off the primes
of `x b`. This packages Prop 5.1 (Kazhdan–Patterson), Lemmas 5.3–5.4, the local Weyl lift identity of
Lemma 6.2 and the two orbit unfoldings. -/

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

open Classical in
/-- The candidate cut (see the module doc). -/
def L3V_CutKP (n : ℕ) (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪),
    let lsym : Ideal (𝓞 F) → F → ℂ := fun P t =>
      if h : ∃ yz : SInt 𝔪 × SInt 𝔪, yz.2 ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
          (yz.2 : F) * t = (yz.1 : F) then
        sexticResidueSymbol ι 𝔪 P h.choose.1 * starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P h.choose.2)
      else 0
    let ladd : Ideal (𝓞 F) → F → ℂ := fun P w =>
      if h : ∃ yzr : SInt 𝔪 × SInt 𝔪 × SInt 𝔪, yzr.2.1 ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
          yzr.2.2 ∈ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
          (yzr.2.1 : F) * (w - (yzr.1 : F)) = (yzr.2.2 : F) then
        sAddChar 𝔪 (-((h.choose.1 : F) / (g.gen P : F)))
      else 0
    let Wv : Ideal (𝓞 F) → ℕ → ℂ := fun P e =>
      if e % 3 = 0 then (((Ideal.absNorm P : ℝ) ^ (-((e / 3 : ℕ) : ℝ)) : ℝ) : ℂ)
      else if e % 3 = 1 then
        (((Ideal.absNorm P : ℝ) ^ (-((e / 3 : ℕ) : ℝ) - 1 / 2) : ℝ) : ℂ) * gaussPhase g 2 P
      else 0
    let Wsph : Ideal (𝓞 F) → ℤ → F → ℂ := fun P e₀ t =>
      if e₀ < 0 then 0 else lsym P t ^ (2 * e₀.toNat) * Wv P e₀.toNat
    let tau : Ideal (𝓞 F) → ℕ → ℂ := fun P j =>
      ∑ᶠ v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)),
        starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P (quotLift v)) ^ j *
          sAddChar 𝔪 (-((quotLift v : F) / (g.gen P : F)))
    let mask : (P : Ideal (𝓞 F)) → ℕ → (SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪))) → ℂ :=
      fun P j v =>
        if j = 0 then (if v = 0 then 1 - (Ideal.absNorm P : ℂ)⁻¹ else -(Ideal.absNorm P : ℂ)⁻¹)
        else (tau P j)⁻¹ * starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P (quotLift v)) ^ j
    let Wweyl : (P : Ideal (𝓞 F)) → ℤ → F → (SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪))) → ℂ :=
      fun P e₀ t v =>
        if e₀ + 2 < 0 then 0 else
          Wv P (e₀ + 2).toNat * lsym P t ^ (4 + 2 * (e₀ + 2).toNat) *
            sexticResidueSymbol ι 𝔪 P (quotLift v) ^ 4 *
            ladd P ((g.gen P : F) ^ (e₀ + 2).toNat * t / (quotLift v : F))
    let Eloc : Ideal (𝓞 F) → ℕ → ℤ → F → ℂ := fun P k e₀ t =>
      if k = 0 then Wsph P e₀ t else
        ∑ᶠ v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)),
          mask P (k % 6) v * (if v = 0 then Wsph P e₀ t else Wweyl P e₀ t v)
    ∃ (V : ℝ → ℝ) (rr : ℕ) (C₀ A₀ : ℝ), Measurable V ∧ 0 < C₀ ∧ 0 < A₀ ∧
      (∀ s : ℂ, -(5 / 6 : ℝ) < s.re →
        MellinConvergent (fun t => (V t : ℂ)) s ∧
        mellin (fun t => (V t : ℂ)) s =
          (C₀ : ℂ) * (A₀ : ℂ) ^ s * (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ rr) ∧
    ∃ (𝒱 : Type) (_ : CommGroup 𝒱) (_ : Fintype 𝒱) (cls : F → 𝒱) (L : SClass 𝔪 → F → ℂ)
      (H : SClass 𝔪 → 𝒱 → ℝ → ℂ) (α : ℝ), 0 < α ∧
      (∀ a b : F, a ≠ 0 → b ≠ 0 → cls (a * b) = cls a * cls b) ∧
      (∀ ε : SUnit 𝔪, cls (((ε : Fˣ) : F) ^ 6) = 1) ∧
      (∀ υ (a b : F), a ≠ 0 → b ≠ 0 → L υ (a * b) = L υ a * L υ b) ∧
      (∀ υ (a : F), a ≠ 0 → ‖L υ a‖ = 1) ∧
      (∀ υ (ε : SUnit 𝔪), L υ ((ε : Fˣ) : F) = 1) ∧
      (∀ υ κ, ContDiff ℝ 2 (fun t => H υ κ (Real.exp t))) ∧
      (∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ υ κ, ∀ j : ℕ, j ≤ 2 → ∀ t : ℝ,
        ‖iteratedDeriv j (fun t => H υ κ (Real.exp t)) t‖ ≤
          C * min (Real.exp (α * t)) (Real.exp (-(N * t)))) ∧
      ∀ (r : RowClass 𝔪) (l : ℝ), 0 < l →
        ∑' p : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠} ×
            {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫},
          gaussPhase g 2 p.1.1 /
              ((Real.sqrt (Ideal.absNorm p.1.1) * Ideal.absNorm p.2.1 : ℝ) : ℂ) *
            χ.thetaChar g (p.1.1 * p.2.1 ^ 3) *
            residueSymbol ι 𝔪 (p.1.1 * p.2.1 ^ 3) (rowElt g r) *
            ((V (Ideal.absNorm (p.1.1 * p.2.1 ^ 3) * l) : ℝ) : ℂ) =
          ∑' z : RowClass 𝔪,
            (∏ P ∈ (normalizedFactors (z.1.1 * r.1.1)).toFinset,
              Eloc P ((normalizedFactors r.1.1).count P)
                (((normalizedFactors z.1.1).count P : ℤ) -
                  2 * ((normalizedFactors r.1.1).count P : ℤ))
                ((rowElt g z : F) / (g.gen r.1.1 : F) ^ 2 *
                  (g.gen P : F) ^ (-(((normalizedFactors z.1.1).count P : ℤ) -
                    2 * ((normalizedFactors r.1.1).count P : ℤ))))) *
            (L r.2 ((rowElt g z : F) / (g.gen r.1.1 : F) ^ 2))⁻¹ *
            H r.2 (cls ((rowElt g z : F) / (g.gen r.1.1 : F) ^ 2))
              ((Ideal.absNorm z.1.1 : ℝ) / ((Ideal.absNorm r.1.1 : ℝ) ^ 2 * l))

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3V_Defs: local symbols at an exterior prime, on elements of `F`

Internal definitions; the cut `L3V_CutKP` inlines them as `let`s (no new bundle):
* `localSymbol ι 𝔪 P t`: `χ_P(t)` for a `P`-unit `t ∈ F` (as `χ_P(y) conj χ_P(z)` for any
  `t = y / z` with `y, z ∈ R` prime to `P`), and `0` if `t` is not a `P`-unit;
* `localAddChar g P w`: `ψ_P(w / p)` for a `P`-integral `w ∈ F`, `p = gen P`, i.e. `e(−y / p)` for
  any `y ∈ R` with `y ≡ w (mod P)`.
-/

namespace ArtinPrimitiveRoots

namespace L3V

open NumberField

variable {F : Type*} [Field F] [NumberField F]

open Classical in
/-- The sextic residue symbol `χ_P(t)` of a `P`-unit `t ∈ F`: `χ_P(y) · conj χ_P(z)` for a
representation `z t = y` with `y, z ∈ R` and `z ∉ P R` (a choice; the value does not depend on it);
`0` if there is none, and `0` (through `χ_P(y) = 0`) when `t ∈ P`. -/
noncomputable def localSymbol (ι : F →+* ℂ) (𝔪 P : Ideal (𝓞 F)) (t : F) : ℂ :=
  if h : ∃ yz : SInt 𝔪 × SInt 𝔪, yz.2 ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
      (yz.2 : F) * t = (yz.1 : F) then
    sexticResidueSymbol ι 𝔪 P h.choose.1 * starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P h.choose.2)
  else 0

open Classical in
/-- The local additive character `ψ_P(w / p)` of the standard character at the exterior prime `P`,
for `P`-integral `w ∈ F`, with `p` the allowed generator of `P`: `e(−y / p)` for some `y ∈ R` with
`z (w − y) ∈ P R` for some `z ∈ R ∖ P R` (a choice; `0` if there is none). By the product formula
`ψ_P(y / p) = conj e(y / p) = e(−y / p)` for `y ∈ R`. -/
noncomputable def localAddChar {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪)
    (P : Ideal (𝓞 F)) (w : F) : ℂ :=
  if h : ∃ yzr : SInt 𝔪 × SInt 𝔪 × SInt 𝔪, yzr.2.1 ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
      yzr.2.2 ∈ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
      (yzr.2.1 : F) * (w - (yzr.1 : F)) = (yzr.2.2 : F) then
    sAddChar 𝔪 (-((h.choose.1 : F) / (g.gen P : F)))
  else 0

end L3V

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3V_Base: the local data of `L3V_CutKP` as top-level definitions, and the cut's data

* `Wv`, `Wsph`, `tau`, `mask`, `Wweyl`, `Eloc`: the `let`s of `L3V_CutKP`; `Rsum`: the nonzero-digit
  part of `Eloc`.
* `Data χ g`: the objects the cut provides for one `(𝔪, χ, g)`; `data_of_cut`.
-/

namespace ArtinPrimitiveRoots

namespace L3V

open NumberField UniqueFactorizationMonoid

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-- `W_P(a(p^e))` of (5.4). -/
noncomputable def Wv (g : AllowedGen ι 𝔪) (P : Ideal (𝓞 F)) (e : ℕ) : ℂ :=
  if e % 3 = 0 then (((Ideal.absNorm P : ℝ) ^ (-((e / 3 : ℕ) : ℝ)) : ℝ) : ℂ)
  else if e % 3 = 1 then
    (((Ideal.absNorm P : ℝ) ^ (-((e / 3 : ℕ) : ℝ) - 1 / 2) : ℝ) : ℂ) * gaussPhase g 2 P
  else 0

/-- `W_P(a(p^{e₀} t))`. -/
noncomputable def Wsph (g : AllowedGen ι 𝔪) (P : Ideal (𝓞 F)) (e₀ : ℤ) (t : F) : ℂ :=
  if e₀ < 0 then 0 else localSymbol ι 𝔪 P t ^ (2 * e₀.toNat) * Wv g P e₀.toNat

/-- `τ_{P,j}`. -/
noncomputable def tau (g : AllowedGen ι 𝔪) (P : Ideal (𝓞 F)) (j : ℕ) : ℂ :=
  ∑ᶠ v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)),
    starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P (quotLift v)) ^ j *
      sAddChar 𝔪 (-((quotLift v : F) / (g.gen P : F)))

open Classical in
/-- The mask `α_{P,j}` of (6.4). -/
noncomputable def mask (g : AllowedGen ι 𝔪) (P : Ideal (𝓞 F)) (j : ℕ)
    (v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪))) : ℂ :=
  if j = 0 then (if v = 0 then 1 - (Ideal.absNorm P : ℂ)⁻¹ else -(Ideal.absNorm P : ℂ)⁻¹)
  else (tau g P j)⁻¹ * starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P (quotLift v)) ^ j

/-- The per-digit Weyl value `W_P(a(p^{e−2} t) w n(v/p))`, `e = e₀ + 2`. -/
noncomputable def Wweyl (g : AllowedGen ι 𝔪) (P : Ideal (𝓞 F)) (e₀ : ℤ) (t : F)
    (v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪))) : ℂ :=
  if e₀ + 2 < 0 then 0 else
    Wv g P (e₀ + 2).toNat * localSymbol ι 𝔪 P t ^ (4 + 2 * (e₀ + 2).toNat) *
      sexticResidueSymbol ι 𝔪 P (quotLift v) ^ 4 *
      localAddChar g P ((g.gen P : F) ^ (e₀ + 2).toNat * t / (quotLift v : F))

open Classical in
/-- The exterior local factor `E_P`. -/
noncomputable def Eloc (g : AllowedGen ι 𝔪) (P : Ideal (𝓞 F)) (k : ℕ) (e₀ : ℤ) (t : F) : ℂ :=
  if k = 0 then Wsph g P e₀ t else
    ∑ᶠ v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)),
      mask g P (k % 6) v * (if v = 0 then Wsph g P e₀ t else Wweyl g P e₀ t v)

open Classical in
/-- The nonzero-digit part of `E_P`. -/
noncomputable def Rsum (g : AllowedGen ι 𝔪) (P : Ideal (𝓞 F)) (j : ℕ) (e₀ : ℤ) (t : F) : ℂ :=
  ∑ᶠ v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)),
    mask g P j v * (if v = 0 then 0 else Wweyl g P e₀ t v)

/-- The monomial exponent `b(j, e)` of (6.15). -/
def bexp (j e : ℕ) : ℕ := if e = 0 then 8 + 5 * j else 4 + 2 * e

/-- `ν = x / b²` for the frequency class `z` and row `r`. -/
noncomputable def nu (g : AllowedGen ι 𝔪) (r z : RowClass 𝔪) : F :=
  (rowElt g z : F) / (g.gen r.1.1 : F) ^ 2

/-- `v_P(ν)`. -/
noncomputable def e0 (r z : RowClass 𝔪) (P : Ideal (𝓞 F)) : ℤ :=
  ((normalizedFactors z.1.1).count P : ℤ) - 2 * ((normalizedFactors r.1.1).count P : ℤ)

/-- The exterior product `∏_P E_P(ν)`. -/
noncomputable def Eprod (g : AllowedGen ι 𝔪) (r z : RowClass 𝔪) : ℂ :=
  ∏ P ∈ (normalizedFactors (z.1.1 * r.1.1)).toFinset,
    Eloc g P ((normalizedFactors r.1.1).count P) (e0 r z P)
      (nu g r z * (g.gen P : F) ^ (-(e0 r z P)))

/-- The forward theta average (Cut63V's left side). -/
noncomputable def fwd (g : AllowedGen ι 𝔪) (χ : HeckeChar F 𝔪) (V : ℝ → ℝ) (r : RowClass 𝔪)
    (l : ℝ) : ℂ :=
  ∑' p : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠} ×
      {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫},
    gaussPhase g 2 p.1.1 /
        ((Real.sqrt (Ideal.absNorm p.1.1) * Ideal.absNorm p.2.1 : ℝ) : ℂ) *
      χ.thetaChar g (p.1.1 * p.2.1 ^ 3) *
      residueSymbol ι 𝔪 (p.1.1 * p.2.1 ^ 3) (rowElt g r) *
      ((V (Ideal.absNorm (p.1.1 * p.2.1 ^ 3) * l) : ℝ) : ℂ)

/-- The data provided by the cut for one `(𝔪, χ, g)`. -/
structure Data (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) where
  V : ℝ → ℝ
  𝒱 : Type
  grp : CommGroup 𝒱
  fin : Fintype 𝒱
  cls : F → 𝒱
  L : SClass 𝔪 → F → ℂ
  H : SClass 𝔪 → 𝒱 → ℝ → ℂ
  α : ℝ
  hα : 0 < α
  hcls : ∀ a b : F, a ≠ 0 → b ≠ 0 → cls (a * b) = cls a * cls b
  hcls6 : ∀ ε : SUnit 𝔪, cls (((ε : Fˣ) : F) ^ 6) = 1
  hL : ∀ υ (a b : F), a ≠ 0 → b ≠ 0 → L υ (a * b) = L υ a * L υ b
  hLn : ∀ υ (a : F), a ≠ 0 → ‖L υ a‖ = 1
  hLu : ∀ υ (ε : SUnit 𝔪), L υ ((ε : Fˣ) : F) = 1
  hH : ∀ υ κ, ContDiff ℝ 2 (fun t => H υ κ (Real.exp t))
  hHb : ∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ υ κ, ∀ j : ℕ, j ≤ 2 → ∀ t : ℝ,
    ‖iteratedDeriv j (fun t => H υ κ (Real.exp t)) t‖ ≤
      C * min (Real.exp (α * t)) (Real.exp (-(N * t)))
  hid : ∀ (r : RowClass 𝔪) (l : ℝ), 0 < l →
    fwd g χ V r l = ∑' z : RowClass 𝔪, Eprod g r z * (L r.2 (nu g r z))⁻¹ *
      H r.2 (cls (nu g r z)) ((Ideal.absNorm z.1.1 : ℝ) / ((Ideal.absNorm r.1.1 : ℝ) ^ 2 * l))

attribute [instance] Data.grp Data.fin

/-- The `V`-clause of the cut (shared with Cut63V). -/
def VClause (V : ℝ → ℝ) : Prop :=
  ∃ (rr : ℕ) (C₀ A₀ : ℝ), Measurable V ∧ 0 < C₀ ∧ 0 < A₀ ∧
    (∀ s : ℂ, -(5 / 6 : ℝ) < s.re →
      MellinConvergent (fun t => (V t : ℂ)) s ∧
      mellin (fun t => (V t : ℂ)) s =
        (C₀ : ℂ) * (A₀ : ℂ) ^ s * (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ rr)

theorem data_of_cut (n : ℕ) (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) (h : L3V_CutKP n F ι) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪), ∃ D : Data χ g, VClause D.V := by
  obtain ⟨N₀, hN⟩ := h
  refine ⟨N₀, fun 𝔪 h𝔪 hs χ g => ?_⟩
  obtain ⟨V, rr, C₀, A₀, hV, hC₀, hA₀, hM, 𝒱, grp, fin, cls, L, H, α, hα, hcls, hcls6, hL, hLn,
    hLu, hH, hHb, hid⟩ := hN 𝔪 h𝔪 hs χ g
  exact ⟨⟨V, 𝒱, grp, fin, cls, L, H, α, hα, hcls, hcls6, hL, hLn, hLu, hH, hHb, hid⟩,
    rr, C₀, A₀, hV, hC₀, hA₀, hM⟩

end L3V

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3V_VP: the `P`-adic valuation `vP` and the unit-part symbol `uSym` (definitions and the
valuation algebra) -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

open Classical in
/-- The `P`-adic valuation `v_P(x) ∈ ℤ` (`0` if `P` is not a nonzero prime). -/
noncomputable def vP (P : Ideal (𝓞 F)) (x : F) : ℤ :=
  if h : P.IsPrime ∧ P ≠ ⊥ then
    -log ((⟨P, h.1, h.2⟩ : HeightOneSpectrum (𝓞 F)).valuation F x)
  else 0

/-- The symbol `χ_P(x p^{−v_P(x)})` of the unit part of `x` at `P` (`p = gen P`). -/
noncomputable def uSym (g : AllowedGen ι 𝔪) (P : Ideal (𝓞 F)) (x : F) : ℂ :=
  localSymbol ι 𝔪 P (x * (g.gen P : F) ^ (-(vP P x)))

lemma vP_v (x : F) : vP v.asIdeal x = -log (v.valuation F x) := by
  unfold vP
  rw [dif_pos ⟨v.isPrime, v.ne_bot⟩]

lemma val_eq_exp_vP {x : F} (hx : x ≠ 0) : v.valuation F x = exp (-(vP v.asIdeal x)) := by
  rw [vP_v, neg_neg, exp_log]
  exact (Valuation.ne_zero_iff _).2 hx

lemma vP_mul {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    vP v.asIdeal (x * y) = vP v.asIdeal x + vP v.asIdeal y := by
  rw [vP_v, vP_v, vP_v, map_mul, log_mul ((Valuation.ne_zero_iff _).2 hx)
    ((Valuation.ne_zero_iff _).2 hy)]
  ring

lemma vP_inv (x : F) : vP v.asIdeal x⁻¹ = -vP v.asIdeal x := by
  rw [vP_v, vP_v, map_inv₀, log_inv, neg_neg]

end L3V

end ArtinPrimitiveRoots

end
end

section
section
namespace ArtinPrimitiveRoots

open NumberField Filter Topology

/-! L2D: ideal counting in a number field. -/

variable {F : Type*} [Field F] [NumberField F]

lemma L2D_finite_le (t : ℝ) : {I : Ideal (𝓞 F) | (Ideal.absNorm I : ℝ) ≤ t}.Finite :=
  (Ideal.finite_setOfPred_absNorm_le ⌊t⌋₊).subset fun I hI => Nat.le_floor hI

/-- The finite set of ideals of norm `≤ t` (including `⊥`). -/
noncomputable def L2D_le (F : Type*) [Field F] [NumberField F] (t : ℝ) : Finset (Ideal (𝓞 F)) :=
  (L2D_finite_le (F := F) t).toFinset

@[simp] lemma L2D_mem_le {t : ℝ} {I : Ideal (𝓞 F)} :
    I ∈ L2D_le F t ↔ (Ideal.absNorm I : ℝ) ≤ t := by
  simp [L2D_le]

end ArtinPrimitiveRoots

end
end

section
section
namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

/-! L2D: candidate cuts beneath C1b (Proposition 4.1 (4.5)).

* `L2D_Cut64`: Lemma 6.4 (p. 38), the quadratic large sieve for `χ_𝔡(c)^3`
  (Goldmakher–Louvel, Thm 1.1).
* `L2D_Cut63`: Lemma 6.3 (p. 34) with (6.22) (p. 33), the reflected expansion of `B_m(Z)`, with
  the coefficients, row/column functions and profiles existentially quantified and only their
  stated bounds retained. -/

/-- `β_p(e)` of (6.20) (p. 33), at a prime of norm `q`. -/
noncomputable def L2D_betaP (q : ℝ) (e : ℕ) : ℝ :=
  if e = 0 then 1
  else if e % 3 = 1 then q ^ (-((e / 3 : ℕ) : ℝ))
  else if e % 3 = 0 then q ^ ((1 : ℝ) / 2 - ((e / 3 : ℕ) : ℝ))
  else 0

open Classical in
/-- `β_𝔣(𝔞')` of (6.20): the product of `β_p(v_p(𝔞'))` over the primes `p ∣ 𝔣`, and `0` when
`𝔞'` has a prime factor outside `𝔣` (so it vanishes off `A(𝔣)`). -/
noncomputable def L2D_beta {F : Type*} [Field F] [NumberField F] (𝔣 𝔞 : Ideal (𝓞 F)) : ℝ :=
  if ∀ P ∈ normalizedFactors 𝔞, P ∣ 𝔣 then
    ∏ P ∈ (normalizedFactors 𝔣).toFinset,
      L2D_betaP (Ideal.absNorm P) ((normalizedFactors 𝔞).count P)
  else 0

end ArtinPrimitiveRoots

end
end

section
section
/-!
# T12B: elementary Euler-product glue for `HeckeChar.LSeries`

* `T12B.norm_le_one`: `‖χ I‖ ≤ 1` (values on coprime ideals are roots of unity: class group and
  `(𝓞/𝔪)ˣ` are finite).
* `T12B.lseries_eq_tsum`: `L(s, χ) = ∑'_I χ(I) N(I)^{-s}` for `Re s > 1`.
* `T12B.sieve`: `(∑' g) · ∏_{P ∈ T} (1 − g P) = ∑'_{I coprime to T} g I` for completely
  multiplicative `g` (finite Euler sieve; no infinite product needed).
* `T12B.sieve_bound`: the sieved sum is close to `1` once `T` kills a large finite set.
-/

namespace ArtinPrimitiveRoots

open NumberField Filter Topology
open scoped nonZeroDivisors

namespace T12B

variable {F : Type*} [Field F] [NumberField F]

/-! ### Summability of `∑_I N(I)^{-σ}` -/

theorem lseriesSummable_card {y : ℝ} (hy : 1 < y) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)) y := by
  have hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℝ)) / (n : ℝ)) atTop
      (𝓝 (dedekindZeta_residue F)) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ F).comp tendsto_natCast_atTop_atTop).congr
      fun n ↦ ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
    congr
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = 0} by
        simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq
        (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (f := fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ))
    (Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using hlim))
    (fun _ ↦ Nat.cast_nonneg _) zero_le_one (s := (y : ℂ)) (by simpa using hy)
  simpa using h

instance fiber_finite (n : ℕ) : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOfPred_absNorm_eq n).to_subtype

/-- `∑_I N(I)^{-σ}` converges for `σ > 1`. -/
theorem summable_absNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun I : Ideal (𝓞 F) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ)) := by
  let e := Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 F) => Ideal.absNorm I)
  rw [← e.summable_iff]
  refine (summable_sigma_of_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)).2
    ⟨fun n => Summable.of_finite, ?_⟩
  refine (lseriesSummable_card (F := F) hσ).norm.congr fun n => ?_
  have hfib : ∀ y : {I : Ideal (𝓞 F) // Ideal.absNorm I = n},
      ((Ideal.absNorm (e ⟨n, y⟩) : ℕ) : ℝ) ^ (-σ) = (n : ℝ) ^ (-σ) := fun y => by
    simp [e, Equiv.sigmaFiberEquiv, y.2]
  simp only [Function.comp_apply, hfib, tsum_const, nsmul_eq_mul, LSeries.norm_term_eq,
    Complex.ofReal_re, Complex.norm_natCast]
  split_ifs with hn
  · subst hn
    rw [Nat.cast_zero, Real.zero_rpow (by linarith), mul_zero]
  · rw [Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]

/-! ### Basic facts on Hecke characters -/

/-! ### The Dirichlet series as a sum over ideals -/

/-! ### The finite sieve -/

end T12B

end ArtinPrimitiveRoots

end
end

section
section
namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

/-! L2D: factorization combinatorics for the proof of (4.5). -/

variable {F : Type*} [Field F] [NumberField F]

/-- The number of distinct prime factors. -/
noncomputable def L2D_omega (I : Ideal (𝓞 F)) : ℕ := (normalizedFactors I).toFinset.card

lemma L2D_prime_of_mem {I P : Ideal (𝓞 F)} (hP : P ∈ normalizedFactors I) : Prime P :=
  prime_of_normalized_factor P hP

lemma L2D_two_le_absNorm {I P : Ideal (𝓞 F)} (hP : P ∈ normalizedFactors I) :
    2 ≤ Ideal.absNorm P := by
  have hp := L2D_prime_of_mem hP
  have h0 : Ideal.absNorm P ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hp.ne_zero
  have h1 : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    intro h; exact hp.not_isUnit (Ideal.isUnit_iff.2 h)
  omega

lemma L2D_eq_of_nf_eq {a b : Ideal (𝓞 F)} (ha : a ≠ ⊥) (hb : b ≠ ⊥)
    (h : normalizedFactors a = normalizedFactors b) : a = b := by
  have h1 := prod_normalizedFactors ha
  have h2 := prod_normalizedFactors hb
  rw [associated_iff_eq] at h1 h2
  rw [← h1, ← h2, h]

lemma L2D_mem_nf_of_dvd {f Q : Ideal (𝓞 F)} (hf : f ≠ ⊥) (hQ : Prime Q) (hQf : Q ∣ f) :
    Q ∈ normalizedFactors f := by
  obtain ⟨Q', hQ', hassoc⟩ := exists_mem_normalizedFactors_of_dvd hf hQ.irreducible hQf
  rw [associated_iff_eq] at hassoc
  rwa [hassoc]

/-! ### `β_p` and the sum of `β_𝔣` -/

/-- The geometric constant bounding `∑_e β_p(e)`. -/
noncomputable def L2D_E0 : ℝ := 2 / (1 - (2 : ℝ) ^ (-(1 / 3 : ℝ)))

lemma L2D_r_lt_one : (2 : ℝ) ^ (-(1 / 3 : ℝ)) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

lemma L2D_r_pos : 0 < (2 : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity

lemma L2D_betaP_nonneg (q : ℝ) (hq : 0 ≤ q) (e : ℕ) : 0 ≤ L2D_betaP q e := by
  unfold L2D_betaP
  split_ifs <;> first | exact Real.rpow_nonneg hq _ | norm_num

lemma L2D_betaP_le (q : ℝ) (hq : 2 ≤ q) (e : ℕ) :
    L2D_betaP q e ≤ 2 * ((2 : ℝ) ^ (-(1 / 3 : ℝ))) ^ e := by
  have hr : ((2 : ℝ) ^ (-(1 / 3 : ℝ))) ^ e = (2 : ℝ) ^ (-((e : ℝ) / 3)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; ring_nf
  rw [hr]
  -- write e = 3k + j
  set k := e / 3 with hk
  have he : (e : ℝ) = 3 * k + (e % 3 : ℕ) := by
    have := Nat.div_add_mod e 3
    exact_mod_cast this.symm
  have hmod : e % 3 < 3 := Nat.mod_lt _ (by norm_num)
  -- `q^x ≤ 2^x` for `x ≤ 0`
  have hq2 : ∀ x : ℝ, x ≤ 0 → q ^ x ≤ (2 : ℝ) ^ x := fun x hx =>
    Real.rpow_le_rpow_of_nonpos (by norm_num) hq hx
  unfold L2D_betaP
  split_ifs with h0 h1 h2
  · subst h0; norm_num
  · -- e = 3k + 1
    have hk' : (e : ℝ) = 3 * k + 1 := by rw [he, h1]; push_cast; ring
    calc q ^ (-(k : ℝ)) ≤ (2 : ℝ) ^ (-(k : ℝ)) := hq2 _ (by simp)
      _ ≤ 2 * (2 : ℝ) ^ (-((e : ℝ) / 3)) := by
        rw [hk']
        have : (2 : ℝ) ^ (-(k : ℝ)) = 2 * (2 : ℝ) ^ (-(k : ℝ) - 1) := by
          rw [Real.rpow_sub (by norm_num), Real.rpow_one]; field_simp
        rw [this]
        gcongr
        · norm_num
        · linarith
  · -- e = 3k, k ≥ 1
    have hk' : (e : ℝ) = 3 * k := by rw [he, h2]; push_cast; ring
    have hk1 : (1 : ℝ) ≤ k := by
      have : 1 ≤ k := by omega
      exact_mod_cast this
    calc q ^ ((1 : ℝ) / 2 - k) ≤ (2 : ℝ) ^ ((1 : ℝ) / 2 - k) := hq2 _ (by linarith)
      _ ≤ (2 : ℝ) ^ ((1 : ℝ) - k) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 * (2 : ℝ) ^ (-((e : ℝ) / 3)) := by
        rw [hk', Real.rpow_sub (by norm_num), Real.rpow_one]
        rw [show -(3 * (k : ℝ) / 3) = -(k : ℝ) by ring, Real.rpow_neg (by norm_num)]
        ring
  · positivity

lemma L2D_sum_betaP_le (q : ℝ) (hq : 2 ≤ q) (M : ℕ) :
    ∑ e ∈ Finset.range M, L2D_betaP q e ≤ L2D_E0 := by
  set r := (2 : ℝ) ^ (-(1 / 3 : ℝ))
  have hr0 : 0 ≤ r := L2D_r_pos.le
  have hr1 : r < 1 := L2D_r_lt_one
  calc ∑ e ∈ Finset.range M, L2D_betaP q e ≤ ∑ e ∈ Finset.range M, 2 * r ^ e :=
        Finset.sum_le_sum fun e _ => L2D_betaP_le q hq e
    _ = 2 * ∑ e ∈ Finset.range M, r ^ e := by rw [Finset.mul_sum]
    _ ≤ 2 * ∑' e : ℕ, r ^ e := by
        gcongr
        exact Summable.sum_le_tsum _ (fun _ _ => by positivity)
          (summable_geometric_of_lt_one hr0 hr1)
    _ = L2D_E0 := by rw [tsum_geometric_of_lt_one hr0 hr1]; unfold L2D_E0; ring

open Classical in
lemma L2D_beta_nonneg (𝔣 𝔞 : Ideal (𝓞 F)) : 0 ≤ L2D_beta 𝔣 𝔞 := by
  unfold L2D_beta
  split_ifs
  · exact Finset.prod_nonneg fun P _ => L2D_betaP_nonneg _ (Nat.cast_nonneg _) _
  · exact le_rfl

open Classical in
/-- `∑_{𝔞 ∈ s} β_𝔣(𝔞) ≤ E₀^{ω(𝔣)}` for every finite set `s` of nonzero ideals. -/
lemma L2D_sum_beta_le (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥) (s : Finset (Ideal (𝓞 F)))
    (hs : ∀ a ∈ s, a ≠ ⊥) :
    ∑ a ∈ s, L2D_beta 𝔣 a ≤ L2D_E0 ^ L2D_omega 𝔣 := by
  let Pf := (normalizedFactors 𝔣).toFinset
  let ι := {P // P ∈ Pf}
  let φ : Ideal (𝓞 F) → ι → ℕ := fun a P => (normalizedFactors a).count P.1
  let supp : Ideal (𝓞 F) → Prop := fun a => ∀ P ∈ normalizedFactors a, P ∣ 𝔣
  let s' := s.filter supp
  let M := ∑ a ∈ s', Multiset.card (normalizedFactors a) + 1
  let g : (ι → ℕ) → ℝ := fun e => ∏ i : ι, L2D_betaP (Ideal.absNorm i.1) (e i)
  have hβ : ∀ a ∈ s', L2D_beta 𝔣 a = g (φ a) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    unfold L2D_beta
    rw [if_pos ha.2]
    exact (Finset.prod_coe_sort Pf (fun P => L2D_betaP (Ideal.absNorm P)
      ((normalizedFactors a).count P))).symm
  have hzero : ∑ a ∈ s, L2D_beta 𝔣 a = ∑ a ∈ s', L2D_beta 𝔣 a := by
    rw [Finset.sum_filter_of_ne]
    intro a _ hne
    by_contra hns
    apply hne
    unfold L2D_beta
    rw [if_neg hns]
  have hinj : Set.InjOn φ s' := by
    intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq, s'] at ha hb
    apply L2D_eq_of_nf_eq (hs a ha.1) (hs b hb.1)
    ext Q
    by_cases hQ : Q ∈ Pf
    · exact congr_fun hab ⟨Q, hQ⟩
    · have hQa : Q ∉ normalizedFactors a := by
        intro hm
        exact hQ (Multiset.mem_toFinset.2
          (L2D_mem_nf_of_dvd h𝔣 (L2D_prime_of_mem hm) (ha.2 Q hm)))
      have hQb : Q ∉ normalizedFactors b := by
        intro hm
        exact hQ (Multiset.mem_toFinset.2
          (L2D_mem_nf_of_dvd h𝔣 (L2D_prime_of_mem hm) (hb.2 Q hm)))
      rw [Multiset.count_eq_zero_of_notMem hQa, Multiset.count_eq_zero_of_notMem hQb]
  have hsub : s'.image φ ⊆ Fintype.piFinset (fun _ : ι => Finset.range M) := by
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨a, ha, rfl⟩ := he
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    have h1 : (normalizedFactors a).count i.1 ≤ Multiset.card (normalizedFactors a) :=
      Multiset.count_le_card _ _
    have h2 : Multiset.card (normalizedFactors a) ≤
        ∑ a ∈ s', Multiset.card (normalizedFactors a) :=
      Finset.single_le_sum (f := fun a => Multiset.card (normalizedFactors a))
        (fun _ _ => Nat.zero_le _) ha
    change (normalizedFactors a).count i.1 < M
    omega
  have hg0 : ∀ e, 0 ≤ g e := fun e =>
    Finset.prod_nonneg fun i _ => L2D_betaP_nonneg _ (Nat.cast_nonneg _) _
  calc ∑ a ∈ s, L2D_beta 𝔣 a = ∑ a ∈ s', L2D_beta 𝔣 a := hzero
    _ = ∑ a ∈ s', g (φ a) := Finset.sum_congr rfl hβ
    _ = ∑ e ∈ s'.image φ, g e := (Finset.sum_image hinj).symm
    _ ≤ ∑ e ∈ Fintype.piFinset (fun _ : ι => Finset.range M), g e :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun e _ _ => hg0 e
    _ = ∏ i : ι, ∑ n ∈ Finset.range M, L2D_betaP (Ideal.absNorm i.1) n :=
        by rw [Finset.prod_univ_sum]
    _ ≤ ∏ _i : ι, L2D_E0 := by
        apply Finset.prod_le_prod
        · intro i _
          exact Finset.sum_nonneg fun n _ => L2D_betaP_nonneg _ (Nat.cast_nonneg _) _
        · intro i _
          apply L2D_sum_betaP_le
          have := L2D_two_le_absNorm (Multiset.mem_toFinset.1 i.2)
          exact_mod_cast this
    _ = L2D_E0 ^ L2D_omega 𝔣 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]; rfl
open Classical in
lemma L2D_simplePart_dvd (𝔟 : Ideal (𝓞 F)) (h𝔟 : 𝔟 ≠ ⊥) : simplePart 𝔟 ∣ 𝔟 := by
  unfold simplePart
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id]
  have hle : ((normalizedFactors 𝔟).toFinset.filter
      fun P => (normalizedFactors 𝔟).count P = 1).val ≤ normalizedFactors 𝔟 := by
    rw [Finset.filter_val, Multiset.toFinset_val]
    exact (Multiset.filter_le _ _).trans (Multiset.dedup_le _)
  have h1 := Multiset.prod_dvd_prod_of_le hle
  have h2 := prod_normalizedFactors h𝔟
  rw [associated_iff_eq] at h2
  rw [h2] at h1
  exact h1


lemma L2D_simplePart_ne_bot (𝔟 : Ideal (𝓞 F)) (h𝔟 : 𝔟 ≠ ⊥) : simplePart 𝔟 ≠ ⊥ := by
  intro h
  have hd := L2D_simplePart_dvd 𝔟 h𝔟
  rw [h] at hd
  exact h𝔟 (by simpa using zero_dvd_iff.1 (show (0 : Ideal (𝓞 F)) ∣ 𝔟 from hd))

open Classical in
lemma L2D_simplePart_nf (𝔟 : Ideal (𝓞 F)) :
    normalizedFactors (simplePart 𝔟) =
      ((normalizedFactors 𝔟).toFinset.filter fun P => (normalizedFactors 𝔟).count P = 1).val := by
  unfold simplePart
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id]
  apply normalizedFactors_prod_of_prime
  intro P hP
  rw [Finset.mem_val, Finset.mem_filter, Multiset.mem_toFinset] at hP
  exact L2D_prime_of_mem hP.1

lemma L2D_simplePart_squarefree (𝔟 : Ideal (𝓞 F)) (h𝔟 : 𝔟 ≠ ⊥) : Squarefree (simplePart 𝔟) := by
  classical
  rw [squarefree_iff_nodup_normalizedFactors (L2D_simplePart_ne_bot 𝔟 h𝔟), L2D_simplePart_nf]
  exact Finset.nodup _

/-- Powerful ideals: nonzero, every prime exponent `≥ 2`. -/
def L2D_Powerful (h : Ideal (𝓞 F)) : Prop :=
  h ≠ ⊥ ∧ ∀ P ∈ normalizedFactors h, 2 ≤ (normalizedFactors h).count P

lemma L2D_powerful_of_mul (𝔟 h : Ideal (𝓞 F)) (h𝔟 : 𝔟 ≠ ⊥) (hh : h * simplePart 𝔟 = 𝔟) :
    L2D_Powerful h := by
  classical
  have hh0 : h ≠ ⊥ := by
    rintro rfl; apply h𝔟; rw [← hh]; simp
  refine ⟨hh0, fun P hP => ?_⟩
  have hnf := normalizedFactors_mul hh0 (L2D_simplePart_ne_bot 𝔟 h𝔟)
  rw [hh, L2D_simplePart_nf] at hnf
  have hc := congr_arg (Multiset.count P) hnf
  rw [Multiset.count_add] at hc
  have hpos : 1 ≤ (normalizedFactors h).count P := Multiset.one_le_count_iff_mem.2 hP
  by_cases h1 : (normalizedFactors 𝔟).count P = 1
  · have hmem : P ∈ ((normalizedFactors 𝔟).toFinset.filter
        fun P => (normalizedFactors 𝔟).count P = 1) := by
      rw [Finset.mem_filter, Multiset.mem_toFinset]
      exact ⟨Multiset.one_le_count_iff_mem.1 (by omega), h1⟩
    have : Multiset.count P ((normalizedFactors 𝔟).toFinset.filter
        fun P => (normalizedFactors 𝔟).count P = 1).val = 1 :=
      Multiset.count_eq_one_of_mem (Finset.nodup _) hmem
    omega
  · have hnm : P ∉ ((normalizedFactors 𝔟).toFinset.filter
        fun P => (normalizedFactors 𝔟).count P = 1) := by
      rw [Finset.mem_filter]; tauto
    have : Multiset.count P ((normalizedFactors 𝔟).toFinset.filter
        fun P => (normalizedFactors 𝔟).count P = 1).val = 0 :=
      Multiset.count_eq_zero_of_notMem hnm
    omega

lemma L2D_nf_subset_of_dvd {f h : Ideal (𝓞 F)} (hh : h ≠ ⊥) (hfh : f ∣ h) :
    (normalizedFactors f).toFinset ⊆ (normalizedFactors h).toFinset := by
  classical
  intro P hP
  rw [Multiset.mem_toFinset] at *
  have hf : f ≠ ⊥ := by rintro rfl; exact hh (zero_dvd_iff.1 hfh)
  exact (dvd_iff_normalizedFactors_le_normalizedFactors hf hh).1 hfh |> Multiset.subset_of_le
    |> fun h => h hP

/-- The admissible active products: squarefree `𝔣` with `𝔣² ∣ 𝔥`. -/
noncomputable def L2D_Fset (h : Ideal (𝓞 F)) : Finset (Ideal (𝓞 F)) := by
  classical
  exact (L2D_le F (Ideal.absNorm h)).filter fun f => Squarefree f ∧ f * f ∣ h

lemma L2D_mem_Fset {h f : Ideal (𝓞 F)} (hh : h ≠ ⊥) :
    f ∈ L2D_Fset h ↔ Squarefree f ∧ f * f ∣ h := by
  classical
  unfold L2D_Fset
  rw [Finset.mem_filter, L2D_mem_le]
  constructor
  · exact fun h => h.2
  · intro hf
    refine ⟨?_, hf⟩
    have hd : f ∣ h := (dvd_mul_right f f).trans hf.2
    have hN0 : Ideal.absNorm h ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) (map_dvd Ideal.absNorm hd)


end ArtinPrimitiveRoots

end
end

section
section
/-! # C3B_Norm: the additive character on `R`, the unit ideal, and `a(1,1,1,1) = 1` -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

lemma sAddChar_congr {𝔪 : Ideal (𝓞 F)} (x x' : F)
    (H : ∀ y : F, (x - y ∈ (placesOf 𝔪).integer F) ↔ (x' - y ∈ (placesOf 𝔪).integer F)) :
    sAddChar 𝔪 x = sAddChar 𝔪 x' := by
  classical
  let G : (F → Prop) → ℂ := fun p => if h : ∃ y, p y then
    Complex.exp (-(2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F h.choose : ℚ) : ℂ)) else 0
  have e1 : sAddChar 𝔪 x = G (fun y => x - y ∈ (placesOf 𝔪).integer F ∧
      ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1) := by
    unfold sAddChar; rfl
  have e2 : sAddChar 𝔪 x' = G (fun y => x' - y ∈ (placesOf 𝔪).integer F ∧
      ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1) := by
    unfold sAddChar; rfl
  rw [e1, e2]
  congr 1
  funext y
  exact propext (and_congr_left' (H y))

/-- `e` is invariant under translation by `R`. -/
lemma sAddChar_add_mem {𝔪 : Ideal (𝓞 F)} (x r : F) (hr : r ∈ (placesOf 𝔪).integer F) :
    sAddChar 𝔪 (x + r) = sAddChar 𝔪 x := by
  have key : ∀ y : F, (x + r - y ∈ (placesOf 𝔪).integer F) ↔ (x - y ∈ (placesOf 𝔪).integer F) := by
    intro y
    constructor
    · intro h
      have := sub_mem h hr
      rwa [show x + r - y - r = x - y by ring] at this
    · intro h
      have := add_mem h hr
      rwa [show x - y + r = x + r - y by ring] at this
  exact sAddChar_congr _ _ key

/-- `e` is trivial on `R`. -/
lemma sAddChar_of_mem {𝔪 : Ideal (𝓞 F)} (x : F) (hx : x ∈ (placesOf 𝔪).integer F) :
    sAddChar 𝔪 x = 1 := by
  have hex : ∃ y : F, x - y ∈ (placesOf 𝔪).integer F ∧
      ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1 :=
    ⟨0, by simpa using hx, fun v _ => by simp⟩
  rw [sAddChar, dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  set y := hex.choose
  have hy : y ∈ (placesOf 𝔪).integer F := by
    have := sub_mem hx h1
    rwa [sub_sub_cancel] at this
  have hall : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F y ≤ 1 := by
    intro v
    by_cases hv : v ∈ placesOf 𝔪
    · exact h2 v hv
    · exact hy v hv
  obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F y hall
  have htr : Algebra.trace ℚ F y = ((Algebra.trace ℤ (𝓞 F) z : ℤ) : ℚ) := by
    rw [← hz, Algebra.coe_trace_int]
  rw [htr]
  have := Complex.exp_int_mul_two_pi_mul_I (-(Algebra.trace ℤ (𝓞 F) z))
  rw [← this]
  congr 1
  push_cast
  ring

/-- The generator of the unit ideal is a unit of `R`. -/
lemma isUnit_gen_top {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) :
    IsUnit (g.gen ⊤) := by
  have h := g.span_gen ⊤ ⟨top_ne_bot, top_sup_eq _⟩
  rw [Ideal.map_top] at h
  exact Ideal.span_singleton_eq_top.mp h

lemma normalizedFactors_top : normalizedFactors (⊤ : Ideal (𝓞 F)) = 0 := by
  rw [← Ideal.one_eq_top, normalizedFactors_one]

lemma residueSymbol_top (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 ⊤ x = 1 := by
  simp [residueSymbol, normalizedFactors_top]

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3B_Unit: `U_S⁶`-invariance of `poissonFactor`, and `u = 1` for the principal class

* `exists_sub_mem_map`: `𝓞/P → R/PR` is onto for `P ∉ S`; hence Fermat in `R/PR`.
* `sexticResidueSymbol_unit_pow_six`: `χ_P(μ⁶ x) = χ_P(x)` when `6 ∣ N P − 1`.
* `poissonFactor_unit_pow_six`: `F(𝔰, 𝔄, μ⁶ h) = F(𝔰, 𝔄, h)` for exterior `𝔰, 𝔄` whose prime
  factors all have `6 ∣ N P − 1`.
* `freqElt_principalFreq`: the principal frequency element is `μ⁶` for an `S`-unit `μ`.
-/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

section residue

variable {𝔪 : Ideal (𝓞 F)}

lemma coe_algebraMap_SInt (x : 𝓞 F) :
    ((algebraMap (𝓞 F) (SInt 𝔪) x : SInt 𝔪) : F) = (x : F) := rfl

lemma card_quot (P : Ideal (𝓞 F)) (hP0 : P ≠ ⊥) [Fintype (𝓞 F ⧸ P)] :
    Fintype.card (𝓞 F ⧸ P) = Ideal.absNorm P := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

end residue

section gen

variable {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

lemma gen_ne_zero (g : AllowedGen ι 𝔪) (I : Ideal (𝓞 F)) (hI : IsExterior 𝔪 I) :
    ((g.gen I : SInt 𝔪) : F) ≠ 0 := by
  intro h0
  have h0' : g.gen I = 0 := Subtype.ext h0
  have hs := g.span_gen I hI
  rw [h0', Ideal.span_singleton_eq_bot.mpr rfl] at hs
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI.1
  have : algebraMap (𝓞 F) (SInt 𝔪) a ∈ I.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
    Ideal.mem_map_of_mem _ ha
  rw [← hs, Ideal.mem_bot] at this
  apply ha0
  have := congrArg (fun z : SInt 𝔪 => (z : F)) this
  simp only [coe_algebraMap_SInt, ZeroMemClass.coe_zero] at this
  exact_mod_cast this

lemma mem_map_iff (g : AllowedGen ι 𝔪) (I : Ideal (𝓞 F)) (hI : IsExterior 𝔪 I) (x : SInt 𝔪) :
    x ∈ I.map (algebraMap (𝓞 F) (SInt 𝔪)) ↔ ∃ r : SInt 𝔪, x = g.gen I * r := by
  rw [← g.span_gen I hI, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨r, hr⟩; exact ⟨r, by rw [← hr, mul_comm]⟩
  · rintro ⟨r, hr⟩; exact ⟨r, by rw [hr, mul_comm]⟩

lemma div_gen_mem (g : AllowedGen ι 𝔪) (I : Ideal (𝓞 F)) (hI : IsExterior 𝔪 I) (x : SInt 𝔪)
    (hx : x ∈ I.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    (x : F) / (g.gen I : F) ∈ (placesOf 𝔪).integer F := by
  obtain ⟨r, rfl⟩ := (mem_map_iff g I hI x).mp hx
  have h0 := gen_ne_zero g I hI
  rw [Subalgebra.coe_mul, mul_div_cancel_left₀ _ h0]
  exact r.2

end gen

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3B_Good: exterior primes satisfy `6 ∣ N P − 1` once `S` contains the primes above `2, 3` -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

/-- A prime of norm divisible by the rational prime `p` has norm at most `p^[F:ℚ]`. -/
theorem absNorm_le_of_prime_dvd (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 F)) (hP0 : P ≠ ⊥)
    [P.IsMaximal] (hpd : p ∣ Ideal.absNorm P) :
    Ideal.absNorm P ≤ p ^ Module.finrank ℤ (𝓞 F) := by
  let _ := Ideal.Quotient.field P
  have : Finite (𝓞 F ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP0
  let _ : Fintype (𝓞 F ⧸ P) := Fintype.ofFinite _
  have hcard := card_quot P hP0
  obtain ⟨f, hq, hpf⟩ := FiniteField.card (𝓞 F ⧸ P) (ringChar (𝓞 F ⧸ P))
  rw [hcard] at hpf
  rw [hpf] at hpd
  have hpq : p = ringChar (𝓞 F ⧸ P) :=
    (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hpd)
  have hp0 : ((p : ℕ) : 𝓞 F ⧸ P) = 0 := by rw [hpq]; exact ringChar.Nat.cast_ringChar
  have hmem : (p : 𝓞 F) ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact hp0
  have hle : Ideal.span {(p : 𝓞 F)} ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hmem
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
  rw [Ideal.absNorm_span_singleton] at hdvd
  have hn : Algebra.norm ℤ (p : 𝓞 F) = (p : ℤ) ^ Module.finrank ℤ (𝓞 F) := by
    rw [show (p : 𝓞 F) = algebraMap ℤ (𝓞 F) p by simp, Algebra.norm_algebraMap]
  rw [hn, Int.natAbs_pow, Int.natAbs_natCast] at hdvd
  exact Nat.le_of_dvd (pow_pos hp.pos _) hdvd

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3B_Main: (7.16)–(7.17) at `u = 1` from four arithmetic cuts

With `b(𝔠, 𝔫, 𝔰, 𝔯) = γ₂(𝔠) ϑ(𝔠𝔫³) F(𝔰, 𝔠𝔫³, gen(𝔯)⁶)` (the coefficient at `u = 1`, without the
`S`-unit `u`), the target `exists_cutoff_freqCoeff_principalFreq_eq_one_and_eq_mul` follows from

* `CutMul`: cross-prime multiplicativity `b(P^{e₀}𝔠, P^l𝔫, P^k𝔰, P^m𝔯) = b(P^{e₀},P^l,P^k,P^m) b(𝔠,𝔫,𝔰,𝔯)`
  ((7.14), (7.16): Chinese remainders + reciprocity (3.3));
* `CutF`: the local Poisson factor `F(P^k, P^{e₀}(P^l)³, gen(P^m)⁶)` ((7.15), (7.17));
* `CutHD`: `γ₁(P) γ₂(P) Λ̄(P) Ḡ(P) = −1` (Davenport–Hasse, (3.9)–(3.11));
* `CutG6`: `Ḡ(P)⁶ = 1`.

Proved here: `a(1,1,1,1) = 1` (`C3B_Norm`), the `U_S⁶`-invariance replacing `u` by `1`
(`C3B_Unit`, `C3B_Good`), `ϑ` on prime powers, `Λ⁶ = jacobiPhaseSix`, and the table algebra. -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

/-! ### Elementary lemmas -/

lemma normalizedFactors_prime_pow {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) (t : ℕ) :
    normalizedFactors (P ^ t) = Multiset.replicate t P := by
  have hirr : Irreducible P := (Ideal.prime_of_isPrime hP0 hP).irreducible
  rw [normalizedFactors_pow, normalizedFactors_irreducible hirr, normalize_eq,
    Multiset.nsmul_singleton]

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3I_Res: the residue rings `R / P^j R` at a prime `P ∉ S`

For a height-one prime `v` of `𝓞 F` outside `S = placesOf 𝔪`:
* `mem_map_pow_iff`: `r ∈ v^j R ↔ v(r) ≤ exp(-j)` for `r ∈ R`;
* `quotEquiv`: `𝓞/v^j ≃+* R/v^j R`; `natCard_quot`: `#(R/v^j R) = N(v)^j`;
* `isMaximal_map`: `v R` is maximal;
* `finsum_quot_fibre`: summing a function that only depends on the class mod `v^i R`
  over `R/v^j R` (`i ≤ j`) gives `N(v)^(j-i)` times the sum over `R/v^i R`.
-/

set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

section val

variable {v : HeightOneSpectrum (𝓞 F)}

lemma coe_alg (a : 𝓞 F) : ((algebraMap (𝓞 F) (SInt 𝔪) a : SInt 𝔪) : F) = algebraMap (𝓞 F) F a :=
  rfl

lemma val_le_one (hv : v ∉ placesOf 𝔪) (r : SInt 𝔪) : v.valuation F (r : F) ≤ 1 := r.2 v hv

lemma val_alg (a : 𝓞 F) : v.valuation F (algebraMap (𝓞 F) F a) = v.intValuation a :=
  v.valuation_of_algebraMap a

/-- Elements of `v^j R` have valuation at most `exp(-j)`. -/
lemma val_le_of_mem (hv : v ∉ placesOf 𝔪) (j : ℕ) {r : SInt 𝔪}
    (hr : r ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪))) :
    v.valuation F (r : F) ≤ exp (-(j : ℤ)) := by
  rw [Ideal.map] at hr
  induction hr using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rw [coe_alg, val_alg]
    exact (v.intValuation_le_pow_iff_mem a j).2 ha
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Subalgebra.coe_add]
    exact (Valuation.map_add _ _ _).trans (max_le hx hy)
  | smul a x _ hx =>
    rw [smul_eq_mul, Subalgebra.coe_mul, map_mul]
    calc v.valuation F (a : F) * v.valuation F (x : F) ≤ 1 * exp (-(j : ℤ)) :=
          mul_le_mul' (val_le_one hv a) hx
      _ = _ := one_mul _

/-- An element of `𝓞` not in `v` has an inverse modulo `v^j`. -/
lemma exists_mul_sub_one_mem (j : ℕ) {d : 𝓞 F} (hd : d ∉ v.asIdeal) :
    ∃ c : 𝓞 F, c * d - 1 ∈ v.asIdeal ^ j := by
  have h1 : IsCoprime v.asIdeal (Ideal.span {d}) := by
    obtain ⟨y, i, hi, hyi⟩ := v.isMaximal.exists_inv hd
    exact Ideal.isCoprime_iff_exists.mpr ⟨i, hi, y * d, Ideal.mul_mem_left _ _
      (Ideal.mem_span_singleton_self d), by rw [add_comm]; exact hyi⟩
  obtain ⟨i, hi, x, hx, hix⟩ := (h1.pow_left (m := j)).exists
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  refine ⟨c, ?_⟩
  have : c * d - 1 = -i := by linear_combination hix
  rw [this]
  exact neg_mem hi

/-- Every `x ∈ F` with `v(x) ≤ 1` is congruent modulo `v^j` (in valuation) to an element of `𝓞`. -/
lemma exists_val_sub_le (j : ℕ) (x : F) (hx : v.valuation F x ≤ 1) :
    ∃ a : 𝓞 F, v.valuation F (x - algebraMap (𝓞 F) F a) ≤ exp (-(j : ℤ)) := by
  obtain ⟨n, ⟨d, hd⟩, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer (K := F) x hx
  obtain ⟨c, hc⟩ := exists_mul_sub_one_mem (v := v) j hd
  refine ⟨c * n, ?_⟩
  have hvd : v.valuation F (algebraMap (𝓞 F) F d) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hd
  have heq : x - algebraMap (𝓞 F) F (c * n) =
      -(x * algebraMap (𝓞 F) F (c * d - 1)) := by
    have hnd' : x * algebraMap (𝓞 F) F d = algebraMap (𝓞 F) F n := hnd
    rw [map_mul, ← hnd', map_sub, map_mul, map_one]; ring
  rw [heq, Valuation.map_neg, map_mul, val_alg]
  calc v.valuation F x * v.intValuation (c * d - 1) ≤ 1 * exp (-(j : ℤ)) :=
        mul_le_mul' hx ((v.intValuation_le_pow_iff_mem _ j).2 hc)
    _ = _ := one_mul _

/-- Elements of `R` of valuation at most `exp(-j)` lie in `v^j R`. -/
lemma mem_of_val_le (hv : v ∉ placesOf 𝔪) (j : ℕ) (r : SInt 𝔪)
    (h : v.valuation F (r : F) ≤ exp (-(j : ℤ))) :
    r ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  obtain ⟨n, ⟨d, hd⟩, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer (K := F) (r : F) (r.2 v hv)
  have hnd' : (r : F) * algebraMap (𝓞 F) F d = algebraMap (𝓞 F) F n := hnd
  have hvd : v.valuation F (algebraMap (𝓞 F) F d) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hd
  have hn : n ∈ v.asIdeal ^ j := by
    rw [← v.intValuation_le_pow_iff_mem, ← val_alg (v := v), ← hnd', map_mul, hvd, mul_one]
    exact h
  obtain ⟨c, hc⟩ := exists_mul_sub_one_mem (v := v) j hd
  have heq : r = algebraMap (𝓞 F) (SInt 𝔪) (c * n) -
      r * algebraMap (𝓞 F) (SInt 𝔪) (c * d - 1) := by
    apply Subtype.ext
    rw [Subalgebra.coe_sub, Subalgebra.coe_mul, coe_alg, coe_alg, map_mul, map_sub, map_mul,
      map_one, ← hnd']
    ring
  rw [heq]
  exact sub_mem (Ideal.mem_map_of_mem _ (Ideal.mul_mem_left _ _ hn))
    (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hc))

lemma mem_map_pow_iff (hv : v ∉ placesOf 𝔪) (j : ℕ) (r : SInt 𝔪) :
    r ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) ↔
      v.valuation F (r : F) ≤ exp (-(j : ℤ)) :=
  ⟨val_le_of_mem hv j, mem_of_val_le hv j r⟩

lemma alg_mem_map_pow_iff (hv : v ∉ placesOf 𝔪) (j : ℕ) (a : 𝓞 F) :
    algebraMap (𝓞 F) (SInt 𝔪) a ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) ↔
      a ∈ v.asIdeal ^ j := by
  rw [mem_map_pow_iff hv, coe_alg, val_alg, v.intValuation_le_pow_iff_mem]

lemma exists_sub_mem_map_pow (hv : v ∉ placesOf 𝔪) (j : ℕ) (r : SInt 𝔪) :
    ∃ a : 𝓞 F, r - algebraMap (𝓞 F) (SInt 𝔪) a ∈
      (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  obtain ⟨a, ha⟩ := exists_val_sub_le (v := v) j (r : F) (r.2 v hv)
  exact ⟨a, mem_of_val_le hv j _ (by rw [Subalgebra.coe_sub, coe_alg]; exact ha)⟩

/-- Discreteness: a valuation strictly above `exp(-(j+1))` is at least `exp(-j)`. -/
lemma exp_le_of_lt {γ : ℤᵐ⁰} {j : ℤ} (h : exp (j - 1) < γ) : exp j ≤ γ := by
  have hγ : γ ≠ 0 := ne_zero_of_lt h
  rw [← exp_log hγ] at h ⊢
  rw [exp_lt_exp] at h
  rw [exp_le_exp]
  omega

lemma exp_le_val_of_not_mem (hv : v ∉ placesOf 𝔪) (j : ℕ) (r : SInt 𝔪)
    (h : r ∉ (v.asIdeal ^ (j + 1)).map (algebraMap (𝓞 F) (SInt 𝔪))) :
    exp (-(j : ℤ)) ≤ v.valuation F (r : F) := by
  rw [mem_map_pow_iff hv, not_le] at h
  apply exp_le_of_lt
  convert h using 2
  push_cast; ring

lemma le_of_mul_le_mul_ne {a b c : ℤᵐ⁰} (h : a * c ≤ b * c) (hc : c ≠ 0) : a ≤ b := by
  have := mul_le_mul_right h c⁻¹
  rwa [mul_comm c⁻¹, mul_comm c⁻¹, mul_inv_cancel_right₀ hc, mul_inv_cancel_right₀ hc] at this

lemma isExterior_mul {I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (hJ : IsExterior 𝔪 J) :
    IsExterior 𝔪 (I * J) := by
  refine ⟨mul_ne_zero hI.1 hJ.1, ?_⟩
  have h1 : IsCoprime I 𝔪 := Ideal.isCoprime_iff_sup_eq.mpr hI.2
  have h2 : IsCoprime J 𝔪 := Ideal.isCoprime_iff_sup_eq.mpr hJ.2
  exact Ideal.isCoprime_iff_sup_eq.mp (h1.mul_left h2)

lemma isExterior_pow {I : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (n : ℕ) :
    IsExterior 𝔪 (I ^ n) := by
  induction n with
  | zero => rw [pow_zero, Ideal.one_eq_top]; exact ⟨top_ne_bot, top_sup_eq _⟩
  | succ k ih => rw [pow_succ]; exact isExterior_mul ih hI

/-- A uniformizer in `𝓞`. -/
lemma exists_uniformizer : ∃ p : 𝓞 F, v.valuation F (algebraMap (𝓞 F) F p) = exp (-1 : ℤ) := by
  obtain ⟨p, hp⟩ := v.intValuation_exists_uniformizer
  exact ⟨p, by rw [val_alg, hp]⟩

end val

section quot

variable {v : HeightOneSpectrum (𝓞 F)}

/-- `𝓞/v^j → R/v^j R`. -/
noncomputable def quotHom (𝔪 : Ideal (𝓞 F)) (I : Ideal (𝓞 F)) :
    𝓞 F ⧸ I →+* SInt 𝔪 ⧸ I.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
  Ideal.quotientMap _ (algebraMap (𝓞 F) (SInt 𝔪)) Ideal.le_comap_map

lemma quotHom_mk (I : Ideal (𝓞 F)) (a : 𝓞 F) :
    quotHom 𝔪 I (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk (I.map (algebraMap (𝓞 F) (SInt 𝔪))) (algebraMap (𝓞 F) (SInt 𝔪) a) :=
  rfl

lemma quotHom_bijective (hv : v ∉ placesOf 𝔪) (j : ℕ) :
    Function.Bijective (quotHom 𝔪 (v.asIdeal ^ j)) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [quotHom_mk, Ideal.Quotient.eq_zero_iff_mem, alg_mem_map_pow_iff hv] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  · intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := exists_sub_mem_map_pow hv j r
    exact ⟨Ideal.Quotient.mk _ a, by rw [quotHom_mk]; exact (Ideal.Quotient.eq.mpr ha).symm⟩

/-- `𝓞/v^j ≃+* R/v^j R`. -/
noncomputable def quotEquiv (hv : v ∉ placesOf 𝔪) (j : ℕ) :
    𝓞 F ⧸ v.asIdeal ^ j ≃+* SInt 𝔪 ⧸ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) :=
  RingEquiv.ofBijective _ (quotHom_bijective hv j)

lemma finite_quot (hv : v ∉ placesOf 𝔪) (j : ℕ) :
    Finite (SInt 𝔪 ⧸ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  have : Finite (𝓞 F ⧸ v.asIdeal ^ j) :=
    Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero _ v.ne_bot)
  exact Finite.of_equiv _ (quotEquiv hv j).toEquiv

lemma natCard_quot (hv : v ∉ placesOf 𝔪) (j : ℕ) :
    Nat.card (SInt 𝔪 ⧸ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪))) =
      Ideal.absNorm v.asIdeal ^ j := by
  rw [← Nat.card_congr (quotEquiv hv j).toEquiv, ← map_pow, Ideal.absNorm_apply,
    Submodule.cardQuot_apply]

/-- `v R` is a maximal ideal of `R`. -/
lemma isMaximal_map (hv : v ∉ placesOf 𝔪) :
    (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))).IsMaximal := by
  have e := quotEquiv (𝔪 := 𝔪) hv 1
  rw [pow_one] at e
  apply Ideal.Quotient.maximal_of_isField
  have : (v.asIdeal).IsMaximal := v.isMaximal
  have hf : IsField (𝓞 F ⧸ v.asIdeal) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp this
  exact MulEquiv.isField hf e.symm.toMulEquiv

end quot

section fibre

variable {v : HeightOneSpectrum (𝓞 F)}

end fibre

end C3I

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3I_Add: the additive character `e`

* `HasWit 𝔪 x`: `x` has a witness `y` in the definition of `sAddChar` (`x - y ∈ R`, `y` integral
  at `S`). `hasWit_of_mul_mem`: true when `x I ⊆ R` for an ideal `I` coprime to `𝔪`; in particular
  `hasWit_div_gen`: `a / gen 𝔞` for `a ∈ R`, `𝔞` exterior.
* `sAddChar_eq_of_wit`: `e(x) = exp(-2πi Tr y)` for every witness; `sAddChar_add`: `e` is additive
  on elements with witnesses.
* `exists_trace_not_int`: for `P ∤ 𝔇`, some `z ∈ P⁻¹` has `Tr z ∉ ℤ`; `sAddChar_ne_one_of_dual`.
* `exists_sAddChar_ne_one`: primitivity at every level: for `x ∈ R ∖ P^j R` some `r ∈ R` has
  `e(x r / gen(P^j)) ≠ 1`.
-/

set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- `x` has a witness in the definition of `sAddChar`. -/
def HasWit (𝔪 : Ideal (𝓞 F)) (x : F) : Prop :=
  ∃ y : F, x - y ∈ (placesOf 𝔪).integer F ∧ ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1

/-- The value of `e` through any witness. -/
lemma sAddChar_eq_of_wit {x y : F} (h1 : x - y ∈ (placesOf 𝔪).integer F)
    (h2 : ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1) :
    sAddChar 𝔪 x =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F y : ℚ) : ℂ)) := by
  have hex : ∃ y : F, x - y ∈ (placesOf 𝔪).integer F ∧
      ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1 := ⟨y, h1, h2⟩
  rw [sAddChar, dif_pos hex]
  obtain ⟨k1, k2⟩ := hex.choose_spec
  set y' := hex.choose
  have hd : y' - y ∈ (placesOf 𝔪).integer F := by
    have := sub_mem h1 k1
    rwa [show x - y - (x - y') = y' - y by ring] at this
  have hall : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (y' - y) ≤ 1 := by
    intro v
    by_cases hv : v ∈ placesOf 𝔪
    · exact (Valuation.map_sub _ _ _).trans (max_le (k2 v hv) (h2 v hv))
    · exact hd v hv
  obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F _ hall
  have htr : Algebra.trace ℚ F y' = Algebra.trace ℚ F y + ((Algebra.trace ℤ (𝓞 F) z : ℤ) : ℚ) := by
    rw [Algebra.coe_trace_int, show ((z : 𝓞 F) : F) = algebraMap (𝓞 F) F z from rfl, hz, map_sub]
    ring
  rw [htr]
  push_cast
  rw [mul_add, Complex.exp_add]
  have := Complex.exp_int_mul_two_pi_mul_I (-(Algebra.trace ℤ (𝓞 F) z))
  rw [show -(2 * (Real.pi : ℂ) * Complex.I) * ((Algebra.trace ℤ (𝓞 F) z : ℤ) : ℂ) =
      ((-(Algebra.trace ℤ (𝓞 F) z) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring, this,
    mul_one]

/-- `e` is additive on elements with witnesses. -/
lemma sAddChar_add {x x' : F} (h : HasWit 𝔪 x) (h' : HasWit 𝔪 x') :
    sAddChar 𝔪 (x + x') = sAddChar 𝔪 x * sAddChar 𝔪 x' := by
  obtain ⟨y, hy1, hy2⟩ := h
  obtain ⟨y', hy1', hy2'⟩ := h'
  have hs1 : x + x' - (y + y') ∈ (placesOf 𝔪).integer F := by
    rw [show x + x' - (y + y') = (x - y) + (x' - y') by ring]; exact add_mem hy1 hy1'
  have hs2 : ∀ v ∈ placesOf 𝔪, v.valuation F (y + y') ≤ 1 :=
    fun v hv => (Valuation.map_add _ _ _).trans (max_le (hy2 v hv) (hy2' v hv))
  rw [sAddChar_eq_of_wit hs1 hs2, sAddChar_eq_of_wit hy1 hy2, sAddChar_eq_of_wit hy1' hy2',
    ← Complex.exp_add, map_add]
  push_cast
  ring_nf

/-- A witness exists when `x I ⊆ R` for an ideal `I` coprime to `𝔪`. -/
lemma hasWit_of_mul_mem (x : F) (I : Ideal (𝓞 F)) (hI : I ⊔ 𝔪 = ⊤)
    (hx : ∀ i ∈ I, x * algebraMap (𝓞 F) F i ∈ (placesOf 𝔪).integer F) : HasWit 𝔪 x := by
  obtain ⟨b, d, hd, hbd⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  set N := Ideal.absNorm (Ideal.span {d}) with hN
  have hcop : IsCoprime I (𝔪 ^ N) := (Ideal.isCoprime_iff_sup_eq.mpr hI).pow_right
  obtain ⟨i, hi, w, hw, hiw⟩ := hcop.exists
  refine ⟨x * algebraMap (𝓞 F) F w, ?_, fun v hv => ?_⟩
  · have hw' : algebraMap (𝓞 F) F w = 1 - algebraMap (𝓞 F) F i := by
      rw [← map_one (algebraMap (𝓞 F) F), ← hiw, map_add]; ring
    have : x - x * algebraMap (𝓞 F) F w = x * algebraMap (𝓞 F) F i := by
      rw [hw']; ring
    rw [this]; exact hx i hi
  · have hvm : 𝔪 ≤ v.asIdeal := hv
    -- `d ∉ v^N`
    have hdN : d ∉ v.asIdeal ^ N := by
      intro hmem
      have hle : Ideal.span {d} ≤ v.asIdeal ^ N := (Ideal.span_singleton_le_iff_mem _).2 hmem
      have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
      rw [map_pow] at hdvd
      have hN0 : N ≠ 0 := by
        rw [hN, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hd0
      have h2 : 2 ≤ Ideal.absNorm v.asIdeal := by
        have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
          rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
        have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
          rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
        omega
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hdvd
      have h3 : 2 ^ N ≤ Ideal.absNorm v.asIdeal ^ N := Nat.pow_le_pow_left h2 N
      have h4 : N < 2 ^ N := Nat.lt_two_pow_self
      omega
    have hvd : exp (-(N : ℤ)) < v.valuation F (algebraMap (𝓞 F) F d) := by
      rw [val_alg, ← not_le, v.intValuation_le_pow_iff_mem]; exact hdN
    have hvw : v.valuation F (algebraMap (𝓞 F) F w) ≤ exp (-(N : ℤ)) := by
      rw [val_alg, v.intValuation_le_pow_iff_mem]
      exact Ideal.pow_right_mono hvm N hw
    have hdpos : v.valuation F (algebraMap (𝓞 F) F d) ≠ 0 := ne_zero_of_lt hvd
    have hxd : x * algebraMap (𝓞 F) F d = algebraMap (𝓞 F) F b := by
      rw [← hbd, div_mul_cancel₀]
      exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hd0
    have key : v.valuation F (x * algebraMap (𝓞 F) F w) * v.valuation F (algebraMap (𝓞 F) F d) ≤
        1 * v.valuation F (algebraMap (𝓞 F) F d) := by
      rw [← map_mul, show x * algebraMap (𝓞 F) F w * algebraMap (𝓞 F) F d =
        algebraMap (𝓞 F) F b * algebraMap (𝓞 F) F w by rw [← hxd]; ring, map_mul]
      calc v.valuation F (algebraMap (𝓞 F) F b) * v.valuation F (algebraMap (𝓞 F) F w)
          ≤ 1 * v.valuation F (algebraMap (𝓞 F) F d) :=
            mul_le_mul' (v.valuation_le_one b) (hvw.trans hvd.le)
        _ = _ := rfl
    exact le_of_mul_le_mul_ne key hdpos

variable {ι : F →+* ℂ}

/-- `a / gen 𝔞` has a witness. -/
lemma hasWit_div_gen (g : AllowedGen ι 𝔪) (𝔞 : Ideal (𝓞 F)) (h𝔞 : IsExterior 𝔪 𝔞)
    (a : SInt 𝔪) : HasWit 𝔪 ((a : F) / (g.gen 𝔞 : F)) := by
  apply hasWit_of_mul_mem _ 𝔞 h𝔞.2
  intro i hi
  have hm : algebraMap (𝓞 F) (SInt 𝔪) i ∈ 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
    Ideal.mem_map_of_mem _ hi
  have := C3B.div_gen_mem g 𝔞 h𝔞 _ hm
  rw [coe_alg] at this
  rw [show (a : F) / (g.gen 𝔞 : F) * algebraMap (𝓞 F) F i =
    (a : F) * (algebraMap (𝓞 F) F i / (g.gen 𝔞 : F)) by ring]
  exact mul_mem a.2 this

/-- `e(a/c + b/c) = e(a/c) e(b/c)` for `c` an allowed generator. -/
lemma sAddChar_div_gen_add (g : AllowedGen ι 𝔪) (𝔞 : Ideal (𝓞 F)) (h𝔞 : IsExterior 𝔪 𝔞)
    (a b : SInt 𝔪) :
    sAddChar 𝔪 ((a : F) / (g.gen 𝔞 : F) + (b : F) / (g.gen 𝔞 : F)) =
      sAddChar 𝔪 ((a : F) / (g.gen 𝔞 : F)) * sAddChar 𝔪 ((b : F) / (g.gen 𝔞 : F)) :=
  sAddChar_add (hasWit_div_gen g 𝔞 h𝔞 a) (hasWit_div_gen g 𝔞 h𝔞 b)

/-! ### The inverse different -/

/-- For `P ∤ 𝔇`, some `z ∈ P⁻¹` has non-integral trace. -/
lemma exists_trace_not_int (P : Ideal (𝓞 F)) (hP0 : P ≠ ⊥)
    (hD : ¬ differentIdeal ℤ (𝓞 F) ≤ P) :
    ∃ z : F, (∀ p ∈ P, ∃ a : 𝓞 F, z * algebraMap (𝓞 F) F p = algebraMap (𝓞 F) F a) ∧
      ∀ n : ℤ, Algebra.trace ℚ F z ≠ n := by
  rw [differentialIdeal_le_iff (K := ℚ) (L := F) hP0, Submodule.map_le_iff_le_comap] at hD
  rw [SetLike.not_le_iff_exists] at hD
  obtain ⟨z, hz, hz'⟩ := hD
  have hP' : (P : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 := by
    simpa using hP0
  have hz2 : z ∈ ((P : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)⁻¹) := hz
  rw [FractionalIdeal.mem_inv_iff hP'] at hz2
  refine ⟨z, fun p hp => ?_, fun n hn => hz' ?_⟩
  · have := hz2 (algebraMap (𝓞 F) F p) ((FractionalIdeal.mem_coeIdeal _).2 ⟨p, hp, rfl⟩)
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).1 this
    exact ⟨a, ha.symm⟩
  · simp only [Submodule.mem_comap, LinearMap.coe_restrictScalars, Submodule.mem_one]
    exact ⟨n, by rw [hn]; simp⟩

/-- For `P` exterior and `z ∈ P⁻¹` with non-integral trace, `e(z) ≠ 1`. -/
lemma sAddChar_ne_one_of_dual (P : Ideal (𝓞 F)) (hPS : P ⊔ 𝔪 = ⊤) (z : F)
    (hz : ∀ p ∈ P, ∃ a : 𝓞 F, z * algebraMap (𝓞 F) F p = algebraMap (𝓞 F) F a)
    (htr : ∀ n : ℤ, Algebra.trace ℚ F z ≠ n) : sAddChar 𝔪 z ≠ 1 := by
  have hw : ∀ v ∈ placesOf 𝔪, v.valuation F z ≤ 1 := by
    intro v hv
    have hvm : 𝔪 ≤ v.asIdeal := hv
    have hPv : ¬ P ≤ v.asIdeal := by
      intro h
      apply v.isPrime.ne_top
      rw [eq_top_iff, ← hPS]
      exact sup_le h hvm
    obtain ⟨p, hp, hpv⟩ := SetLike.not_le_iff_exists.mp hPv
    obtain ⟨a, ha⟩ := hz p hp
    have h1 : v.valuation F (algebraMap (𝓞 F) F p) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hpv
    have := v.valuation_le_one (K := F) a
    change v.valuation F (algebraMap (𝓞 F) F a) ≤ 1 at this
    rw [← ha, map_mul, h1, mul_one] at this
    exact this
  rw [sAddChar_eq_of_wit (y := z) (by simp) hw]
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  apply htr (-n)
  have h2 : ((Algebra.trace ℚ F z : ℚ) : ℂ) = ((-n : ℤ) : ℂ) := by
    have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    apply mul_left_cancel₀ hpi
    push_cast
    linear_combination -hn
  exact_mod_cast h2

/-! ### Primitivity at every level -/

section prim

variable {v : HeightOneSpectrum (𝓞 F)}

/-- `z (v R) ⊆ R` for `z ∈ v⁻¹`. -/
lemma mul_mem_of_mem_map (z : F)
    (hz : ∀ p ∈ v.asIdeal, ∃ a : 𝓞 F, z * algebraMap (𝓞 F) F p = algebraMap (𝓞 F) F a)
    {y : SInt 𝔪} (hy : y ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    z * (y : F) ∈ (placesOf 𝔪).integer F := by
  rw [Ideal.map] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨a, ha⟩ := hz p hp
    rw [coe_alg, ha]
    exact (algebraMap (𝓞 F) (SInt 𝔪) a).2
  | zero => simp
  | add x y _ _ hx hy => rw [Subalgebra.coe_add, mul_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [smul_eq_mul, Subalgebra.coe_mul, mul_left_comm]
    exact mul_mem a.2 hx

/-- Primitivity of `x ↦ e(x / gen(P^j))` on `R / P^j R`: for `x ∉ P^j R` there is `r ∈ R` with
`e(x r / gen(P^j)) ≠ 1`, when `P ∤ 𝔇`. -/
lemma exists_sAddChar_ne_one (g : AllowedGen ι 𝔪) (hv : v ∉ placesOf 𝔪)
    (hPS : v.asIdeal ⊔ 𝔪 = ⊤) (hD : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) {j : ℕ} (hj : 1 ≤ j)
    (x : SInt 𝔪) (hx : x ∉ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪))) :
    ∃ r : SInt 𝔪, sAddChar 𝔪 ((x : F) * (r : F) / (g.gen (v.asIdeal ^ j) : F)) ≠ 1 := by
  obtain ⟨z, hz, htr⟩ := exists_trace_not_int v.asIdeal v.ne_bot hD
  have hez := sAddChar_ne_one_of_dual v.asIdeal hPS z hz htr
  have hext : IsExterior 𝔪 (v.asIdeal ^ j) :=
    isExterior_pow ⟨v.ne_bot, hPS⟩ j
  set B := g.gen (v.asIdeal ^ j)
  have hB0 : (B : F) ≠ 0 := C3B.gen_ne_zero g _ hext
  have hBmem : B ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← g.span_gen _ hext]; exact Ideal.mem_span_singleton_self _
  have hB1 : B ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    have : (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) ≤
        v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
      Ideal.map_mono (by simpa using Ideal.pow_le_pow_right (I := v.asIdeal) hj)
    exact this hBmem
  -- `w = z B ∈ R`
  have hwR : z * (B : F) ∈ (placesOf 𝔪).integer F := mul_mem_of_mem_map z hz hB1
  set w : SInt 𝔪 := ⟨z * (B : F), hwR⟩
  -- valuations
  have hvz : v.valuation F z ≤ exp (1 : ℤ) := by
    obtain ⟨p, hp⟩ := exists_uniformizer (v := v)
    have hpm : p ∈ v.asIdeal := by
      rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F), hp]
      exact exp_lt_exp.2 (by norm_num) |>.trans_eq exp_zero
    obtain ⟨a, ha⟩ := hz p hpm
    have h1 := v.valuation_le_one (K := F) a
    change v.valuation F (algebraMap (𝓞 F) F a) ≤ 1 at h1
    rw [← ha, map_mul, hp] at h1
    have : v.valuation F z * exp (-1 : ℤ) * exp 1 ≤ 1 * exp 1 := mul_le_mul_left h1 _
    rwa [mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one, one_mul] at this
  have hvB := val_le_of_mem hv j hBmem
  have hvw : v.valuation F (w : F) ≤ exp (1 - (j : ℤ)) := by
    change v.valuation F (z * (B : F)) ≤ _
    rw [map_mul, show (1 - (j : ℤ)) = 1 + (-(j : ℤ)) by ring, exp_add]
    exact mul_le_mul' hvz hvB
  have hvx : exp (1 - (j : ℤ)) ≤ v.valuation F (x : F) := by
    have := exp_le_val_of_not_mem hv (j - 1) x (by rwa [Nat.sub_add_cancel hj])
    convert this using 2
    push_cast [Nat.cast_sub hj]; ring
  have hx0 : (x : F) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hvx
    exact exp_ne_zero (le_antisymm hvx bot_le)
  have hvx0 : v.valuation F (x : F) ≠ 0 := by
    rw [Ne, map_eq_zero]; exact hx0
  -- `f = w / x` is `v`-integral
  have hvf : v.valuation F ((w : F) / (x : F)) ≤ 1 := by
    rw [map_div₀, div_le_one₀ (pos_iff_ne_zero.2 hvx0)]
    exact hvw.trans hvx
  obtain ⟨a, ha⟩ := exists_val_sub_le (v := v) j _ hvf
  -- `w - x a ∈ P^j R`
  set δ : SInt 𝔪 := w - x * algebraMap (𝓞 F) (SInt 𝔪) a
  have hδ : δ ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    apply mem_of_val_le hv j
    have : (δ : F) = (x : F) * ((w : F) / (x : F) - algebraMap (𝓞 F) F a) := by
      simp only [δ, Subalgebra.coe_sub, Subalgebra.coe_mul, coe_alg]
      field_simp
    rw [this, map_mul]
    calc v.valuation F (x : F) * v.valuation F ((w : F) / (x : F) - algebraMap (𝓞 F) F a)
        ≤ 1 * exp (-(j : ℤ)) := mul_le_mul' (val_le_one hv x) ha
      _ = _ := one_mul _
  refine ⟨algebraMap (𝓞 F) (SInt 𝔪) a, fun h1 => hez ?_⟩
  have hzeq : z = (x : F) * ((algebraMap (𝓞 F) (SInt 𝔪) a : SInt 𝔪) : F) / (B : F) +
      (δ : F) / (B : F) := by
    simp only [δ, Subalgebra.coe_sub, Subalgebra.coe_mul]
    change z = _ + (z * (B : F) - _) / (B : F)
    field_simp
    ring
  rw [hzeq, C3B.sAddChar_add_mem _ _ (C3B.div_gen_mem g _ hext δ hδ), h1]

end prim

end C3I

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3M_Base: hypotheses from section A, finite quotients `R/𝔞R`, residue-symbol algebra

* `HypAdd 𝔪`: `e` is additive on `F` (needs the existence of `sAddChar` witnesses).
* `HypChi ι 𝔪`: at every exterior prime `P`, `χ_P` is multiplicative on `R` and `χ_P(x)⁶ = 1`
  for `x ∉ PR`.
-/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F]

/-- Hypothesis (section A): at an exterior prime, the sextic symbol is multiplicative on `R`, with
sixth power `1` off `PR`. -/
def HypChi (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) : Prop :=
  ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P →
    (∀ x y : SInt 𝔪, sexticResidueSymbol ι 𝔪 P (x * y) =
      sexticResidueSymbol ι 𝔪 P x * sexticResidueSymbol ι 𝔪 P y) ∧
    (∀ x : SInt 𝔪, x ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) → sexticResidueSymbol ι 𝔪 P x ^ 6 = 1)

variable {𝔪 : Ideal (𝓞 F)}

/-! ### Ideals -/

lemma exterior_of_mem_factors {𝔞 Q : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    (hQ : Q ∈ normalizedFactors 𝔞) : Q.IsPrime ∧ IsExterior 𝔪 Q := by
  have hpr : Prime Q := prime_of_normalized_factor Q hQ
  refine ⟨Ideal.isPrime_of_prime hpr, hpr.ne_zero, ?_⟩
  have hle : 𝔞 ≤ Q := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hQ)
  exact eq_top_iff.mpr (h𝔞.2 ▸ sup_le_sup_right hle 𝔪)

lemma isExterior_of_mul_left {I J : Ideal (𝓞 F)} (h : IsExterior 𝔪 (I * J)) : IsExterior 𝔪 I := by
  refine ⟨fun h0 => h.1 (by rw [h0, Ideal.bot_mul]), ?_⟩
  exact eq_top_iff.mpr (h.2 ▸ sup_le_sup_right (Ideal.mul_le_inf.trans inf_le_left) 𝔪)

lemma isExterior_of_mul_right {I J : Ideal (𝓞 F)} (h : IsExterior 𝔪 (I * J)) :
    IsExterior 𝔪 J := by
  rw [mul_comm] at h; exact isExterior_of_mul_left h

/-- An exterior prime does not become the unit ideal in `R`. -/
lemma map_ne_top {Q : Ideal (𝓞 F)} (hQ : Q.IsPrime) (hQe : IsExterior 𝔪 Q) :
    Q.map (algebraMap (𝓞 F) (SInt 𝔪)) ≠ ⊤ := by
  intro htop
  let v : HeightOneSpectrum (𝓞 F) := ⟨Q, hQ, hQe.1⟩
  have hvS : v ∉ placesOf 𝔪 := by
    intro hv
    have : (⊤ : Ideal (𝓞 F)) ≤ Q := hQe.2 ▸ sup_le le_rfl hv
    exact hQ.ne_top (eq_top_iff.mpr this)
  let J : Ideal (SInt 𝔪) :=
    { carrier := {x | v.valuation F (x : F) < 1}
      add_mem' := fun {a b} ha hb => by
        show v.valuation F ((a + b : SInt 𝔪) : F) < 1
        rw [Subalgebra.coe_add]
        exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha hb)
      zero_mem' := by
        show v.valuation F ((0 : SInt 𝔪) : F) < 1
        simp
      smul_mem' := fun c x hx => by
        show v.valuation F ((c * x : SInt 𝔪) : F) < 1
        rw [Subalgebra.coe_mul, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (c.2 v hvS)) hx }
  have hle : Q.map (algebraMap (𝓞 F) (SInt 𝔪)) ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    show v.valuation F ((algebraMap (𝓞 F) (SInt 𝔪) a : SInt 𝔪) : F) < 1
    rw [C3B.coe_algebraMap_SInt]
    exact (v.valuation_lt_one_iff_mem a).mpr ha
  have h1 : (1 : SInt 𝔪) ∈ J := hle (htop ▸ Submodule.mem_top)
  have : v.valuation F ((1 : SInt 𝔪) : F) < 1 := h1
  simp at this

/-! ### Residue symbols -/

variable {ι : F →+* ℂ}

lemma residueSymbol_mul_ideal (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 (I * J) x = residueSymbol ι 𝔪 I x * residueSymbol ι 𝔪 J x := by
  unfold residueSymbol
  rw [normalizedFactors_mul hI hJ, Multiset.map_add, Multiset.prod_add]

lemma residueSymbol_prime {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 P x = sexticResidueSymbol ι 𝔪 P x := by
  have h := C3B.normalizedFactors_prime_pow hP hP0 1
  rw [pow_one, Multiset.replicate_one] at h
  simp [residueSymbol, h]

lemma residueSymbol_mul (hχ : HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    (x y : SInt 𝔪) :
    residueSymbol ι 𝔪 𝔞 (x * y) = residueSymbol ι 𝔪 𝔞 x * residueSymbol ι 𝔪 𝔞 y := by
  unfold residueSymbol
  rw [← Multiset.prod_map_mul]
  congr 1
  refine Multiset.map_congr rfl fun Q hQ => ?_
  obtain ⟨hQp, hQe⟩ := exterior_of_mem_factors h𝔞 hQ
  exact (hχ Q hQp hQe).1 x y

lemma not_mem_of_isCoprime {I : Ideal (SInt 𝔪)} (hI : I ≠ ⊤) {x : SInt 𝔪}
    (h : IsCoprime (Ideal.span {x}) I) : x ∉ I := by
  intro hx
  apply hI
  rw [Ideal.isCoprime_iff_sup_eq] at h
  rw [eq_top_iff, ← h]
  exact sup_le ((Ideal.span_singleton_le_iff_mem I).mpr hx) le_rfl

lemma residueSymbol_pow_six (hχ : HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    {x : SInt 𝔪} (hx : IsCoprime (Ideal.span {x}) (𝔞.map (algebraMap (𝓞 F) (SInt 𝔪)))) :
    residueSymbol ι 𝔪 𝔞 x ^ 6 = 1 := by
  unfold residueSymbol
  rw [← Multiset.prod_map_pow]
  apply Multiset.prod_eq_one
  intro z hz
  obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.mp hz
  obtain ⟨hQp, hQe⟩ := exterior_of_mem_factors h𝔞 hQ
  apply (hχ Q hQp hQe).2
  apply not_mem_of_isCoprime (map_ne_top hQp hQe)
  have hle : 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪)) ≤ Q.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
    Ideal.map_mono (Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hQ))
  rw [Ideal.isCoprime_iff_sup_eq] at hx ⊢
  exact eq_top_iff.mpr (hx ▸ sup_le_sup_left hle _)

lemma residueSymbol_ne_zero (hχ : HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    {x : SInt 𝔪} (hx : IsCoprime (Ideal.span {x}) (𝔞.map (algebraMap (𝓞 F) (SInt 𝔪)))) :
    residueSymbol ι 𝔪 𝔞 x ≠ 0 := by
  intro h0
  have := residueSymbol_pow_six hχ h𝔞 hx
  rw [h0] at this; norm_num at this

lemma isCoprime_one (I : Ideal (SInt 𝔪)) : IsCoprime (Ideal.span {(1 : SInt 𝔪)}) I := by
  rw [Ideal.span_singleton_one]; exact Ideal.isCoprime_iff_sup_eq.mpr (top_sup_eq _)

lemma residueSymbol_one (hχ : HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞) :
    residueSymbol ι 𝔪 𝔞 1 = 1 := by
  have h := residueSymbol_mul hχ h𝔞 (1 : SInt 𝔪) 1
  rw [one_mul] at h
  have h0 := residueSymbol_ne_zero hχ h𝔞 (isCoprime_one _)
  have : residueSymbol ι 𝔪 𝔞 1 * (residueSymbol ι 𝔪 𝔞 1 - 1) = 0 := by
    rw [mul_sub, ← h]; ring
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd h1 h0
  · exact sub_eq_zero.mp h1

lemma isCoprime_unit (u : (SInt 𝔪)ˣ) (I : Ideal (SInt 𝔪)) :
    IsCoprime (Ideal.span {(u : SInt 𝔪)}) I := by
  rw [Ideal.span_singleton_eq_top.mpr u.isUnit]; exact Ideal.isCoprime_iff_sup_eq.mpr (top_sup_eq _)

lemma residueSymbol_unit_pow_six (hχ : HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    (u : (SInt 𝔪)ˣ) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 𝔞 ((u : SInt 𝔪) ^ 6 * x) = residueSymbol ι 𝔪 𝔞 x := by
  have hp : ∀ n : ℕ, residueSymbol ι 𝔪 𝔞 ((u : SInt 𝔪) ^ n) = residueSymbol ι 𝔪 𝔞 u ^ n := by
    intro n
    induction n with
    | zero => simp [residueSymbol_one hχ h𝔞]
    | succ n ih => rw [pow_succ, residueSymbol_mul hχ h𝔞, ih, pow_succ]
  rw [residueSymbol_mul hχ h𝔞, hp, residueSymbol_pow_six hχ h𝔞 (isCoprime_unit u _), one_mul]

/-! ### Generators -/

/-- `gen(I J) = ε⁶ gen(I) gen(J)` with `ε` a unit of `R`. -/
lemma gen_mul' (g : AllowedGen ι 𝔪) {I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I)
    (hJ : IsExterior 𝔪 J) :
    ∃ ε : (SInt 𝔪)ˣ, g.gen (I * J) = (ε : SInt 𝔪) ^ 6 * g.gen I * g.gen J := by
  obtain ⟨ε, hε⟩ := g.gen_mul I J hI hJ
  refine ⟨Set.unitEquivUnitsInteger (placesOf 𝔪) F ε, ?_⟩
  apply Subtype.ext
  rw [hε]
  simp

lemma gen_top (g : AllowedGen ι 𝔪) : ∃ ε : (SInt 𝔪)ˣ, g.gen ⊤ = (ε : SInt 𝔪) ^ 6 := by
  obtain ⟨ε, hε⟩ := gen_mul' g ⟨top_ne_bot, top_sup_eq _⟩ ⟨top_ne_bot, top_sup_eq _⟩
  rw [Ideal.top_mul] at hε
  obtain ⟨u, hu⟩ := C3B.isUnit_gen_top g
  refine ⟨ε⁻¹, ?_⟩
  have h1 : (u : SInt 𝔪) * 1 = (u : SInt 𝔪) * ((ε : SInt 𝔪) ^ 6 * (u : SInt 𝔪)) := by
    rw [← hu] at hε
    rw [mul_one]
    calc (u : SInt 𝔪) = (ε : SInt 𝔪) ^ 6 * u * u := hε
      _ = _ := by ring
  have h2 := u.isUnit.mul_left_cancel h1
  rw [← hu]
  have h3 : ((ε : SInt 𝔪) ^ 6) * ((↑(ε⁻¹) : SInt 𝔪) ^ 6) = 1 := by
    rw [← mul_pow, Units.mul_inv, one_pow]
  calc (u : SInt 𝔪) = (u : SInt 𝔪) * ((ε : SInt 𝔪) ^ 6 * (↑(ε⁻¹) : SInt 𝔪) ^ 6) := by
        rw [h3, mul_one]
    _ = ((ε : SInt 𝔪) ^ 6 * (u : SInt 𝔪)) * (↑(ε⁻¹) : SInt 𝔪) ^ 6 := by ring
    _ = (↑(ε⁻¹) : SInt 𝔪) ^ 6 := by rw [← h2, one_mul]

end C3M

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3M_Sum: the Poisson sum and the Gauss sum with free generators; CRT and twists

* `PS 𝔰 𝔄 s A Af c h = ∑_{d mod 𝔰} ∑_{v mod 𝔄} [h ≡ Af d (𝔰)] χ_𝔰(d) χ_𝔄(v) e((h − Af d) v c/(sA))`;
  `poissonFactor g 𝔰 𝔄 h = PS 𝔰 𝔄 (gen 𝔰) (gen 𝔄) (gen 𝔄) 1 h`.
* `GS 𝔠 c c' j = ∑_{x mod 𝔠} χ_𝔠(x)^j e(x c'/c)`; `gaussPhase g j 𝔠 = q^{-1/2} GS 𝔠 (gen 𝔠) 1 j`.
* `PS_crt`, `GS_crt`: Chinese remainders with idempotents `β s₂A₂`, `α s₁A₁`.
* `PS_twist`, `GS_twist`: unit substitutions.
-/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F]

section defs

variable (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F))

end defs

variable {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-! ### Generic lemmas -/

/-! ### Coercions -/

/-! ### The Poisson summand -/

section U

variable {𝔰 𝔄 : Ideal (𝓞 F)} {s A Af c h : SInt 𝔪}

end U

/-! ### Field identities -/

/-! ### CRT and twists for `PS` -/

section crt

variable {𝔰₁ 𝔰₂ 𝔄₁ 𝔄₂ : Ideal (𝓞 F)} {s₁ s₂ A₁ A₂ Af c h α β : SInt 𝔪}

end crt

/-! ### Gauss sums -/

section gs

variable {𝔠 : Ideal (𝓞 F)} {c c' : SInt 𝔪} {j : ℕ}

end gs

end C3M

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3M_Mul: twisted multiplicativity of `γ_j`, of `F(𝔰, 𝔄, gen(𝔯)⁶)`, of `ϑ`, and reciprocity

* `gaussPhase_mul` (3.10): `γ_j(𝔠₁𝔠₂) = χ_{𝔠₁}(c₂)^j χ_{𝔠₂}(c₁)^j γ_j(𝔠₁) γ_j(𝔠₂)`.
* `poissonFactor_mul`: for `𝔰₁𝔄₁` coprime to `𝔰₂𝔄₂`, `𝔯ᵢ` coprime to the other side,
  `χ_{𝔰₁}(A₂) χ_{𝔰₂}(A₁) F(𝔰₁𝔰₂, 𝔄₁𝔄₂, gen(𝔯₁𝔯₂)⁶)
     = χ_{𝔄₁}(s₂A₂) χ_{𝔄₂}(s₁A₁) F(𝔰₁, 𝔄₁, gen(𝔯₁)⁶) F(𝔰₂, 𝔄₂, gen(𝔯₂)⁶)`.
* `residueSymbol_gen_prime`: `χ_𝔟(gen P) = χ_P(gen 𝔟)` (from (3.3)).
-/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-! ### Coprimality in `R` -/

/-! ### Change of generators -/

/-! ### Generators and residue symbols -/

lemma residueSymbol_gen_mul (hχ : HypChi ι 𝔪) (g : AllowedGen ι 𝔪) {𝔞 I J : Ideal (𝓞 F)}
    (h𝔞 : IsExterior 𝔪 𝔞) (hI : IsExterior 𝔪 I) (hJ : IsExterior 𝔪 J) :
    residueSymbol ι 𝔪 𝔞 (g.gen (I * J)) =
      residueSymbol ι 𝔪 𝔞 (g.gen I) * residueSymbol ι 𝔪 𝔞 (g.gen J) := by
  obtain ⟨ε, hε⟩ := gen_mul' g hI hJ
  rw [hε, mul_assoc, residueSymbol_unit_pow_six hχ h𝔞, residueSymbol_mul hχ h𝔞]

lemma residueSymbol_gen_top (hχ : HypChi ι 𝔪) (g : AllowedGen ι 𝔪) {𝔞 : Ideal (𝓞 F)}
    (h𝔞 : IsExterior 𝔪 𝔞) : residueSymbol ι 𝔪 𝔞 (g.gen ⊤) = 1 := by
  obtain ⟨ε, hε⟩ := gen_top g
  rw [hε, ← mul_one ((ε : SInt 𝔪) ^ 6), residueSymbol_unit_pow_six hχ h𝔞,
    residueSymbol_one hχ h𝔞]

/-- Extended reciprocity: `χ_𝔟(gen P) = χ_P(gen 𝔟)` for an exterior `𝔟` prime to `P`. -/
lemma residueSymbol_gen_prime (hχ : HypChi ι 𝔪) (g : AllowedGen ι 𝔪) {P : Ideal (𝓞 F)}
    (hP : P.IsPrime) (hPe : IsExterior 𝔪 P) (𝔟 : Ideal (𝓞 F)) :
    IsExterior 𝔪 𝔟 → ¬ 𝔟 ≤ P →
      residueSymbol ι 𝔪 𝔟 (g.gen P) = residueSymbol ι 𝔪 P (g.gen 𝔟) := by
  induction 𝔟 using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd rfl h.1
  | h₂ u hu =>
    intro hue _
    have hu' : u = ⊤ := Ideal.isUnit_iff.mp hu
    subst hu'
    rw [C3B.residueSymbol_top, residueSymbol_gen_top hχ g hPe]
  | h₃ 𝔞 Q _ hQ ih =>
    intro hQa hle
    have hQp : Q.IsPrime := Ideal.isPrime_of_prime hQ
    have hQe : IsExterior 𝔪 Q := isExterior_of_mul_left hQa
    have hae : IsExterior 𝔪 𝔞 := isExterior_of_mul_right hQa
    have hQP : ¬ Q ≤ P := fun h => hle (le_trans Ideal.mul_le_left h)
    have haP : ¬ 𝔞 ≤ P := fun h => hle (le_trans Ideal.mul_le_right h)
    have hne : P ≠ Q := fun h => hQP (h ▸ le_rfl)
    rw [residueSymbol_mul_ideal _ _ hQe.1 hae.1, ih hae haP,
      residueSymbol_gen_mul hχ g hPe hQe hae, residueSymbol_prime hQp hQe.1,
      residueSymbol_prime hP hPe.1, residueSymbol_prime hP hPe.1,
      ← g.reciprocity P Q hP hQp hPe hQe hne]

/-! ### `ϑ` and norms -/

/-! ### (3.10) -/

/-! ### Cross-prime multiplicativity of the Poisson factor -/

end C3M

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3V_Ideal: prime-exponent bookkeeping for ideals of `𝓞 F`

`cnt P I = v_P(I)` (count in `normalizedFactors`), `prim I` its prime support; products, powers,
prime-power products over a finset, ideal equality from exponents, squarefreeness and coprimality
in exponent form, norms; `residueSymbol` over a squarefree ideal, and reciprocity
`χ_𝔠(gen 𝔡) = χ_𝔡(gen 𝔠)` for coprime exterior `𝔠, 𝔡`. -/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F]

/-- `v_P(I)`. -/
noncomputable abbrev cnt (P I : Ideal (𝓞 F)) : ℕ := (normalizedFactors I).count P

/-- The prime support of `I`. -/
noncomputable abbrev prim (I : Ideal (𝓞 F)) : Finset (Ideal (𝓞 F)) := (normalizedFactors I).toFinset

lemma cnt_mul {P I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    cnt P (I * J) = cnt P I + cnt P J := by
  unfold cnt; rw [normalizedFactors_mul hI hJ, Multiset.count_add]

lemma cnt_pow (P I : Ideal (𝓞 F)) (n : ℕ) : cnt P (I ^ n) = n * cnt P I := by
  unfold cnt; rw [normalizedFactors_pow, Multiset.count_nsmul]

lemma nf_prime' {Q : Ideal (𝓞 F)} (hQ : Q.IsPrime) (hQ0 : Q ≠ ⊥) : normalizedFactors Q = {Q} := by
  rw [normalizedFactors_irreducible ((Ideal.prime_of_isPrime hQ0 hQ).irreducible), normalize_eq]

lemma cnt_prime {P Q : Ideal (𝓞 F)} (hQ : Q.IsPrime) (hQ0 : Q ≠ ⊥) :
    cnt P Q = if P = Q then 1 else 0 := by
  unfold cnt; rw [nf_prime' hQ hQ0, Multiset.count_singleton]

lemma cnt_top (P : Ideal (𝓞 F)) : cnt P ⊤ = 0 := by
  unfold cnt; rw [C3B.normalizedFactors_top]; simp

lemma prime_of_mem_prim {P I : Ideal (𝓞 F)} (hP : P ∈ prim I) : P.IsPrime ∧ P ≠ ⊥ := by
  have hp := L2D_prime_of_mem (Multiset.mem_toFinset.1 hP)
  exact ⟨Ideal.isPrime_of_prime hp, hp.ne_zero⟩

lemma prod_pow_ne_bot (s : Finset (Ideal (𝓞 F))) (hs : ∀ Q ∈ s, Q.IsPrime ∧ Q ≠ ⊥)
    (n : Ideal (𝓞 F) → ℕ) : ∏ Q ∈ s, Q ^ n Q ≠ ⊥ := by
  exact Finset.prod_ne_zero_iff.2 fun Q hQ => pow_ne_zero _ (hs Q hQ).2

lemma cnt_prod_pow (P : Ideal (𝓞 F)) (s : Finset (Ideal (𝓞 F)))
    (hs : ∀ Q ∈ s, Q.IsPrime ∧ Q ≠ ⊥) (n : Ideal (𝓞 F) → ℕ) :
    cnt P (∏ Q ∈ s, Q ^ n Q) = if P ∈ s then n P else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cnt_top]
  | insert Q s hQs ih =>
    have hs' : ∀ R ∈ s, R.IsPrime ∧ R ≠ ⊥ := fun R hR => hs R (Finset.mem_insert_of_mem hR)
    have hQ := hs Q (Finset.mem_insert_self Q s)
    rw [Finset.prod_insert hQs, cnt_mul (pow_ne_zero _ hQ.2) (prod_pow_ne_bot s hs' n), cnt_pow,
      cnt_prime hQ.1 hQ.2, ih hs']
    by_cases hPQ : P = Q
    · subst hPQ; simp [hQs]
    · simp [hPQ, Finset.mem_insert]

lemma not_prime_count_zero {P I : Ideal (𝓞 F)} (hP : ¬ (P.IsPrime ∧ P ≠ ⊥)) : cnt P I = 0 := by
  unfold cnt
  rw [Multiset.count_eq_zero]
  intro hm
  exact hP (prime_of_mem_prim (Multiset.mem_toFinset.2 hm))

lemma eq_of_cnt {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (h : ∀ P : Ideal (𝓞 F), P.IsPrime → P ≠ ⊥ → cnt P I = cnt P J) : I = J := by
  apply L2D_eq_of_nf_eq hI hJ
  ext P
  by_cases hP : P.IsPrime ∧ P ≠ ⊥
  · exact h P hP.1 hP.2
  · change cnt P I = cnt P J
    rw [not_prime_count_zero hP, not_prime_count_zero hP]

lemma mem_prim_iff {P I : Ideal (𝓞 F)} : P ∈ prim I ↔ 0 < cnt P I := by
  unfold prim cnt; rw [Multiset.mem_toFinset, Multiset.count_pos]

lemma dvd_iff_cnt_pos {P I : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hI : I ≠ ⊥) :
    P ∣ I ↔ 0 < cnt P I := by
  rw [← mem_prim_iff, Multiset.mem_toFinset]
  constructor
  · exact L2D_mem_nf_of_dvd hI (Ideal.prime_of_isPrime hP0 hP)
  · exact dvd_of_mem_normalizedFactors

lemma squarefree_iff_cnt {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : Squarefree I ↔ ∀ P, cnt P I ≤ 1 := by
  rw [squarefree_iff_nodup_normalizedFactors hI, Multiset.nodup_iff_count_le_one]

lemma sup_eq_top_iff_cnt {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    I ⊔ J = ⊤ ↔ ∀ P, cnt P I = 0 ∨ cnt P J = 0 := by
  constructor
  · intro h P
    by_contra hc
    push Not at hc
    have hP : P.IsPrime ∧ P ≠ ⊥ := by
      by_contra hn; exact hc.1 (not_prime_count_zero hn)
    have h1 := (dvd_iff_cnt_pos hP.1 hP.2 hI).2 (Nat.pos_of_ne_zero hc.1)
    have h2 := (dvd_iff_cnt_pos hP.1 hP.2 hJ).2 (Nat.pos_of_ne_zero hc.2)
    rw [Ideal.dvd_iff_le] at h1 h2
    exact hP.1.ne_top (eq_top_iff.2 (h ▸ sup_le h1 h2))
  · intro h
    by_contra hne
    obtain ⟨M, hM, hIJ⟩ := Ideal.exists_le_maximal _ hne
    have hM0 : M ≠ ⊥ := by
      intro h0; rw [h0] at hIJ; exact hI (eq_bot_iff.2 (le_trans le_sup_left hIJ))
    have h1 := (dvd_iff_cnt_pos hM.isPrime hM0 hI).1 (Ideal.dvd_iff_le.2 (le_trans le_sup_left hIJ))
    have h2 := (dvd_iff_cnt_pos hM.isPrime hM0 hJ).1 (Ideal.dvd_iff_le.2 (le_trans le_sup_right hIJ))
    rcases h M with h3 | h3 <;> omega

lemma exterior_of_prim {𝔪 I P : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (hP : P ∈ prim I) :
    IsExterior 𝔪 P :=
  (C3M.exterior_of_mem_factors hI (Multiset.mem_toFinset.1 hP)).2

lemma exterior_prod_pow {𝔪 : Ideal (𝓞 F)} (s : Finset (Ideal (𝓞 F)))
    (hs : ∀ Q ∈ s, IsExterior 𝔪 Q) (n : Ideal (𝓞 F) → ℕ) : IsExterior 𝔪 (∏ Q ∈ s, Q ^ n Q) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Ideal.one_eq_top]; exact ⟨top_ne_bot, top_sup_eq _⟩
  | insert Q s hQs ih =>
    rw [Finset.prod_insert hQs]
    exact C3I.isExterior_mul (C3I.isExterior_pow (hs Q (Finset.mem_insert_self Q s)) _)
      (ih fun R hR => hs R (Finset.mem_insert_of_mem hR))

lemma prod_prim (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) : ∏ P ∈ prim I, P ^ cnt P I = I := by
  have h := prod_normalizedFactors hI
  rw [associated_iff_eq] at h
  conv_rhs => rw [← h]
  rw [Finset.prod_multiset_count]

lemma absNorm_eq_prod (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    (Ideal.absNorm I : ℝ) = ∏ P ∈ prim I, (Ideal.absNorm P : ℝ) ^ cnt P I := by
  conv_lhs => rw [← prod_prim I hI]
  rw [map_prod]; push_cast
  simp [map_pow]

lemma residueSymbol_sqfree (ι : F →+* ℂ) (𝔪 𝔡 : Ideal (𝓞 F)) (h𝔡 : 𝔡 ≠ ⊥) (hs : Squarefree 𝔡)
    (x : SInt 𝔪) :
    residueSymbol ι 𝔪 𝔡 x = ∏ P ∈ prim 𝔡, sexticResidueSymbol ι 𝔪 P x := by
  unfold residueSymbol prim
  have hnd := (squarefree_iff_nodup_normalizedFactors h𝔡).1 hs
  rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, hnd.dedup]

variable {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-- Reciprocity for coprime exterior ideals: `χ_𝔠(gen 𝔡) = χ_𝔡(gen 𝔠)`. -/
lemma residueSymbol_recip (hχ : C3M.HypChi ι 𝔪) (g : AllowedGen ι 𝔪) {𝔡 : Ideal (𝓞 F)}
    (h𝔡 : IsExterior 𝔪 𝔡) (𝔠 : Ideal (𝓞 F)) :
    IsExterior 𝔪 𝔠 → 𝔠 ⊔ 𝔡 = ⊤ →
      residueSymbol ι 𝔪 𝔠 (g.gen 𝔡) = residueSymbol ι 𝔪 𝔡 (g.gen 𝔠) := by
  induction 𝔠 using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd rfl h.1
  | h₂ u hu =>
    intro _ _
    have hu' : u = ⊤ := Ideal.isUnit_iff.mp hu
    subst hu'
    rw [C3B.residueSymbol_top, C3M.residueSymbol_gen_top hχ g h𝔡]
  | h₃ 𝔞 Q _ hQ ih =>
    intro hQa hcop
    have hQp : Q.IsPrime := Ideal.isPrime_of_prime hQ
    have hQe : IsExterior 𝔪 Q := C3M.isExterior_of_mul_left hQa
    have hae : IsExterior 𝔪 𝔞 := C3M.isExterior_of_mul_right hQa
    have hQd : ¬ 𝔡 ≤ Q := by
      intro hle
      apply hQp.ne_top
      rw [eq_top_iff, ← hcop]
      exact sup_le Ideal.mul_le_left hle
    have hcop' : 𝔞 ⊔ 𝔡 = ⊤ := by
      rw [eq_top_iff, ← hcop]; exact sup_le_sup_right Ideal.mul_le_right _
    rw [C3M.residueSymbol_mul_ideal _ _ hQe.1 hae.1, ih hae hcop',
      C3M.residueSymbol_gen_mul hχ g h𝔡 hQe hae,
      C3M.residueSymbol_gen_prime hχ g hQp hQe 𝔡 h𝔡 hQd]

end L3V

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3V_ValB: the local package `Env` (from `L3V_LocPkg`) and the unit-part symbol calculus

`Env ι 𝔪` records, at every exterior prime, the facts of the local statement `L3V_LocPkg`; from it:
valuations of generators and units, the unit part `x p^{−v_P(x)}`, and `uSym` multiplicative, of
order dividing `6`, equal to `χ_P` on `R ∖ P R`. -/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-- The local facts at one exterior prime. -/
structure LocAt (g : AllowedGen ι 𝔪) (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hPe : IsExterior 𝔪 P) :
    Prop where
  sext_mul : ∀ x y : SInt 𝔪, sexticResidueSymbol ι 𝔪 P (x * y) =
    sexticResidueSymbol ι 𝔪 P x * sexticResidueSymbol ι 𝔪 P y
  sext_six : ∀ x : SInt 𝔪, x ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) →
    sexticResidueSymbol ι 𝔪 P x ^ 6 = 1
  mem_iff : ∀ y : SInt 𝔪, y ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ↔
    (⟨P, hP, hPe.1⟩ : HeightOneSpectrum (𝓞 F)).valuation F (y : F) = 1
  val_gen : ∀ I : Ideal (𝓞 F), IsExterior 𝔪 I →
    (⟨P, hP, hPe.1⟩ : HeightOneSpectrum (𝓞 F)).valuation F (g.gen I : F) =
      exp (-(((normalizedFactors I).count P : ℕ) : ℤ))
  lsym_mul : ∀ t t' : F, (⟨P, hP, hPe.1⟩ : HeightOneSpectrum (𝓞 F)).valuation F t = 1 →
    (⟨P, hP, hPe.1⟩ : HeightOneSpectrum (𝓞 F)).valuation F t' = 1 →
    localSymbol ι 𝔪 P (t * t') = localSymbol ι 𝔪 P t * localSymbol ι 𝔪 P t'
  lsym_six : ∀ t : F, (⟨P, hP, hPe.1⟩ : HeightOneSpectrum (𝓞 F)).valuation F t = 1 →
    localSymbol ι 𝔪 P t ^ 6 = 1
  lsym_SInt : ∀ y : SInt 𝔪, y ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) →
    localSymbol ι 𝔪 P (y : F) = sexticResidueSymbol ι 𝔪 P y
  Eloc_split : ∀ k : ℕ, k ≠ 0 → ∀ (e₀ : ℤ) (t : F),
    Eloc g P k e₀ t = mask g P (k % 6) 0 * Wsph g P e₀ t + Rsum g P (k % 6) e₀ t
  mask_zero : ∀ j : ℕ, j ≠ 0 → mask g P j 0 = 0
  Rsum_mono : ∀ j : ℕ, j < 6 → ∀ e₀ : ℤ, 0 ≤ e₀ + 2 → ∀ t : F,
    (⟨P, hP, hPe.1⟩ : HeightOneSpectrum (𝓞 F)).valuation F t = 1 →
    Rsum g P j e₀ t = Rsum g P j e₀ 1 * localSymbol ι 𝔪 P t ^ bexp j (e₀ + 2).toNat
  Rsum_one : ∀ e₀ : ℤ, 0 < e₀ + 2 → ∀ t : F,
    (⟨P, hP, hPe.1⟩ : HeightOneSpectrum (𝓞 F)).valuation F t ≤ 1 → Rsum g P 1 e₀ t = 0
  Rsum_le : ∀ j : ℕ, j < 6 → ∀ e₀ : ℤ, 0 ≤ e₀ + 2 →
    ‖Rsum g P j e₀ 1‖ ≤ L2D_betaP (Ideal.absNorm P) (e₀ + 2).toNat
  mask_le : ∀ j : ℕ, ‖mask g P j 0‖ ≤ 1
  gp_le : ‖gaussPhase g 2 P‖ ≤ 1

/-- The standing hypotheses at the modulus `𝔪`. -/
structure Env (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) : Prop where
  loc : ∀ (g : AllowedGen ι 𝔪) (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hPe : IsExterior 𝔪 P),
    LocAt g P hP hPe

lemma Env.hχ {E : Env ι 𝔪} (g : AllowedGen ι 𝔪) : C3M.HypChi ι 𝔪 := fun P hP hPe =>
  ⟨(E.loc g P hP hPe).sext_mul, (E.loc g P hP hPe).sext_six⟩

theorem env_of_locPkg (n : ℕ) (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) (h : L3V_LocPkg n F ι) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → Env ι 𝔪 := by
  obtain ⟨N₀, hN⟩ := h
  refine ⟨N₀, fun 𝔪 h𝔪 hs => ⟨fun g P hP hPe => ?_⟩⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hN 𝔪 h𝔪 hs g P hP hPe
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩


section ucalc

variable (E : Env ι 𝔪) (g : AllowedGen ι 𝔪) {P : Ideal (𝓞 F)} (hP : P.IsPrime)
  (he : IsExterior 𝔪 P)
include E hP he

omit E in
lemma notS_of_ext : (⟨P, hP, he.1⟩ : HeightOneSpectrum (𝓞 F)) ∉ placesOf 𝔪 := fun hv =>
  hP.ne_top (eq_top_iff.2 (he.2 ▸ sup_le le_rfl hv))

omit E in
lemma val_le_oneE (r : SInt 𝔪) : (⟨P, hP, he.1⟩ : HeightOneSpectrum (𝓞 F)).valuation F (r : F) ≤ 1 :=
  r.2 _ (notS_of_ext hP he)

omit E in
lemma val_unitE (μ : (SInt 𝔪)ˣ) :
    (⟨P, hP, he.1⟩ : HeightOneSpectrum (𝓞 F)).valuation F ((μ : SInt 𝔪) : F) = 1 := by
  have h1 := val_le_oneE hP he (μ : SInt 𝔪)
  have h2 := val_le_oneE hP he ((μ⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪)
  have h3 : (⟨P, hP, he.1⟩ : HeightOneSpectrum (𝓞 F)).valuation F ((μ : SInt 𝔪) : F) *
      (⟨P, hP, he.1⟩ : HeightOneSpectrum (𝓞 F)).valuation F
        (((μ⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = 1 := by
    rw [← map_mul, ← Subalgebra.coe_mul, Units.mul_inv]; simp
  exact eq_one_of_one_le_mul_left h1 h2 h3.ge

lemma val_piE : (⟨P, hP, he.1⟩ : HeightOneSpectrum (𝓞 F)).valuation F (g.gen P : F) = exp (-1 : ℤ) := by
  rw [(E.loc g P hP he).val_gen P he]
  have : (normalizedFactors P).count P = 1 := by
    have := cnt_prime (P := P) hP he.1; simpa using this
  rw [this]; simp

lemma vP_genE (I : Ideal (𝓞 F)) (hI : IsExterior 𝔪 I) :
    vP P (g.gen I : F) = ((normalizedFactors I).count P : ℤ) := by
  have := vP_v (v := ⟨P, hP, he.1⟩) (g.gen I : F)
  change vP P _ = _ at this
  rw [this, (E.loc g P hP he).val_gen I hI, log_exp, neg_neg]

omit E g in
lemma vP_unitE (μ : (SInt 𝔪)ˣ) : vP P ((μ : SInt 𝔪) : F) = 0 := by
  have := vP_v (v := ⟨P, hP, he.1⟩) ((μ : SInt 𝔪) : F)
  change vP P _ = _ at this
  rw [this, val_unitE hP he]; simp

lemma val_unitPartE {x : F} (hx : x ≠ 0) :
    (⟨P, hP, he.1⟩ : HeightOneSpectrum (𝓞 F)).valuation F (x * (g.gen P : F) ^ (-(vP P x))) = 1 := by
  have h := val_eq_exp_vP (v := ⟨P, hP, he.1⟩) hx
  change _ = exp (-(vP P x)) at h
  rw [map_mul, map_zpow₀, val_piE E g hP he, h, ← exp_zsmul, ← exp_add]
  simp

lemma p_ne_zeroE : (g.gen P : F) ≠ 0 := C3B.gen_ne_zero g P he

lemma uSym_mulE {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    uSym g P (x * y) = uSym g P x * uSym g P y := by
  unfold uSym
  rw [← (E.loc g P hP he).lsym_mul _ _ (val_unitPartE E g hP he hx) (val_unitPartE E g hP he hy)]
  have h := vP_mul (v := ⟨P, hP, he.1⟩) hx hy
  change vP P (x * y) = vP P x + vP P y at h
  rw [h, neg_add, zpow_add₀ (p_ne_zeroE E g hP he)]
  ring_nf

lemma uSym_pow_sixE {x : F} (hx : x ≠ 0) : uSym g P x ^ 6 = 1 :=
  (E.loc g P hP he).lsym_six _ (val_unitPartE E g hP he hx)

lemma uSym_oneE : uSym g P (1 : F) = 1 := by
  have hv1 : (⟨P, hP, he.1⟩ : HeightOneSpectrum (𝓞 F)).valuation F (1 : F) = 1 := map_one _
  have h1 := (E.loc g P hP he).lsym_mul 1 1 hv1 hv1
  have h6 := (E.loc g P hP he).lsym_six 1 hv1
  rw [mul_one] at h1
  have h0 : localSymbol ι 𝔪 P 1 ≠ 0 := by intro h0; rw [h0] at h6; norm_num at h6
  have hl : localSymbol ι 𝔪 P 1 = 1 := by
    have := mul_left_cancel₀ h0 (h1.symm.trans (mul_one _).symm); exact this
  have hvp : vP P (1 : F) = 0 := by
    have := vP_v (v := ⟨P, hP, he.1⟩) (1 : F)
    change vP P _ = _ at this
    rw [this, hv1]; simp
  unfold uSym; rw [hvp, neg_zero, zpow_zero, mul_one, hl]

lemma uSym_powE {x : F} (hx : x ≠ 0) (n : ℕ) : uSym g P (x ^ n) = uSym g P x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, uSym_oneE E g hP he]
  | succ n ih => rw [pow_succ, uSym_mulE E g hP he (pow_ne_zero _ hx) hx, ih, pow_succ]

lemma uSym_invE {x : F} (hx : x ≠ 0) : uSym g P x⁻¹ = (uSym g P x)⁻¹ := by
  have h1 := uSym_mulE E g hP he hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, uSym_oneE E g hP he] at h1
  exact eq_inv_of_mul_eq_one_right h1.symm

lemma uSym_SIntE {y : SInt 𝔪} (hy : y ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    uSym g P (y : F) = sexticResidueSymbol ι 𝔪 P y := by
  have hv := ((E.loc g P hP he).mem_iff y).1 hy
  have hvp : vP P (y : F) = 0 := by
    have := vP_v (v := ⟨P, hP, he.1⟩) (y : F)
    change vP P _ = _ at this
    rw [this, hv]; simp
  unfold uSym; rw [hvp, neg_zero, zpow_zero, mul_one, (E.loc g P hP he).lsym_SInt y hy]

lemma uSym_pow_six_unitE (μ : (SInt 𝔪)ˣ) : uSym g P (((μ : SInt 𝔪) : F) ^ 6) = 1 := by
  have hμ : ((μ : SInt 𝔪) : F) ≠ 0 := by
    intro h0; have := val_unitE hP he μ; rw [h0, map_zero] at this; exact zero_ne_one this
  rw [uSym_powE E g hP he hμ, uSym_pow_sixE E g hP he hμ]

end ucalc

end L3V

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3V_Keys: the coefficients `ω`, `ρ`, `λ` and profiles of (6.23)–(6.25), and their bounds

For the cut data `D` and an enumeration `eU : Fin N ≃ U_S/U_S^6`, slices `s = (u, s_d, s_c)`:
* `omg` = `ω_{υ,𝔱}` (6.23), `rho` = `ρ_{υ,𝔱,s_d}` (6.24), `lam` = `λ_{υ,𝔱,s_c}` (6.25), written with
  the unit-part symbols `uSym`; `Hk` = `H_{υ,κ₆(𝔱;s_d,s_c)}` (6.21);
* `Env`: the standing hypotheses (good exterior primes, `HypChi`, a primitive sixth root);
* the bounds `‖omg‖ ≤ ∏ β`, `‖rho‖ ≤ 1`, `‖lam‖ ≤ 1` and the vanishing of `omg` off `A(𝔣)`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-- The slices `s = (u, s_d, s_c)`. -/
abbrev TT {g : AllowedGen ι 𝔪} {χ : HeckeChar F 𝔪} (D : Data χ g) (N : ℕ) : Type :=
  Fin N × D.𝒱 × D.𝒱

section defs

variable (g : AllowedGen ι 𝔪) {χ : HeckeChar F 𝔪} (D : Data χ g) {N : ℕ} (eU : Fin N ≃ SClass 𝔪)

/-- The frequency-unit representative `ε_u`. -/
noncomputable def urep (u : Fin N) : F := (((eU u).rep : SInt 𝔪) : F)

/-- `j_𝔭 = v_𝔭(𝔥) mod 6`. -/
noncomputable def jP (𝔥 P : Ideal (𝓞 F)) : ℕ := cnt P 𝔥 % 6

/-- `s_{𝔭,j,e} = R_{𝔭,j,e}(1)`. -/
noncomputable def sP (𝔥 P : Ideal (𝓞 F)) (e : ℕ) : ℂ := Rsum g P (jP 𝔥 P) ((e : ℤ) - 2) 1

/-- `b_{j,e}`. -/
noncomputable def bP (𝔥 P : Ideal (𝓞 F)) (e : ℕ) : ℕ := bexp (jP 𝔥 P) e

/-- `ω_𝔭 = R_{𝔭,1,0}(1)` of (6.14). -/
noncomputable def om1 (P : Ideal (𝓞 F)) : ℂ := Rsum g P 1 (-2) 1

/-- The inactive scalar `I_{𝔥,𝔣} = ∏_{𝔭 ∣ 𝔥, 𝔭 ∤ 𝔣} α_{𝔭,j_𝔭}(0)`. -/
noncomputable def Iin (𝔥 𝔣 : Ideal (𝓞 F)) : ℂ := ∏ P ∈ prim 𝔥 \ prim 𝔣, mask g P (jP 𝔥 P) 0

/-- `gen I` in `F`. -/
noncomputable abbrev gF (I : Ideal (𝓞 F)) : F := (g.gen I : F)

open Classical in
/-- `ω_{υ,𝔱}` (6.23). -/
noncomputable def omg (υ : SClass 𝔪) (𝔥 𝔣 𝔞 𝔫 : Ideal (𝓞 F)) (s : TT D N) : ℂ :=
  if IsExterior 𝔪 𝔥 ∧ IsExterior 𝔪 𝔣 ∧ IsExterior 𝔪 𝔞 ∧ IsExterior 𝔪 𝔫 ∧
      (∀ P ∈ normalizedFactors 𝔞, P ∣ 𝔣) ∧ 𝔫 ⊔ 𝔣 = ⊤ then
    Iin g 𝔥 𝔣 * (D.L υ (gF g 𝔞))⁻¹ * ((D.L υ (gF g 𝔫))⁻¹) ^ 3 * D.L υ (gF g 𝔣) ^ 2 *
      ∏ P ∈ prim 𝔣, sP g 𝔥 P (cnt P 𝔞) *
        (uSym g P (urep eU s.1) * uSym g P (gF g 𝔞) * uSym g P (gF g 𝔫) ^ 3 *
          ((uSym g P (gF g 𝔣))⁻¹) ^ 2) ^ bP 𝔥 P (cnt P 𝔞)
  else 0

open Classical in
/-- `ρ_{υ,𝔱,s_d}(𝔡)` (6.24). -/
noncomputable def rho (υ : SClass 𝔪) (𝔥 𝔣 𝔞 𝔫 : Ideal (𝓞 F)) (s : TT D N)
    (𝔡 : Ideal (𝓞 F)) : ℂ :=
  if IsExterior 𝔪 𝔡 ∧ 𝔡 ⊔ 𝔫 = ⊤ ∧ D.cls (gF g 𝔡) = s.2.1 then
    D.L υ (gF g 𝔡) ^ 2 *
      (∏ P ∈ prim 𝔡, om1 g P *
        (uSym g P (urep eU s.1) * uSym g P (gF g 𝔞) * uSym g P (gF g 𝔫) ^ 3 *
          ((uSym g P (gF g 𝔡))⁻¹) ^ 2 * ((uSym g P (gF g 𝔣))⁻¹) ^ 2) ^ 13) *
      ∏ P ∈ prim 𝔣, ((uSym g P (gF g 𝔡))⁻¹) ^ (2 * bP 𝔥 P (cnt P 𝔞))
  else 0

open Classical in
/-- `λ_{υ,𝔱,s_c}(𝔠)` (6.25). -/
noncomputable def lam (υ : SClass 𝔪) (𝔥 𝔣 𝔞 𝔫 : Ideal (𝓞 F)) (s : TT D N)
    (𝔠 : Ideal (𝓞 F)) : ℂ :=
  if IsExterior 𝔪 𝔠 ∧ 𝔠 ⊔ 𝔣 = ⊤ ∧ D.cls (gF g 𝔠) = s.2.2 then
    (D.L υ (gF g 𝔠))⁻¹ * (∏ P ∈ prim 𝔣, uSym g P (gF g 𝔠) ^ bP 𝔥 P (cnt P 𝔞)) *
      ∏ Q ∈ prim 𝔠, gaussPhase g 2 Q *
        (uSym g Q (urep eU s.1) * uSym g Q (gF g 𝔞) * uSym g Q (gF g 𝔠) *
          ((uSym g Q (gF g 𝔣))⁻¹) ^ 2) ^ 2
  else 0

/-- `H_{υ,κ₆}` with `κ₆ = [ε_u][a'] s_c [n']³ s_d^{−2} [f]^{−2}` (6.21). -/
noncomputable def Hk (υ : SClass 𝔪) (_𝔥 𝔣 𝔞 𝔫 : Ideal (𝓞 F)) (s : TT D N) (y : ℝ) : ℂ :=
  D.H υ (D.cls (urep eU s.1) * D.cls (gF g 𝔞) * s.2.2 * D.cls (gF g 𝔫) ^ 3 * (s.2.1 ^ 2)⁻¹ *
    (D.cls (gF g 𝔣) ^ 2)⁻¹) y

end defs

/-! ### Local facts at exterior primes -/

section env

variable (E : Env ι 𝔪) (g : AllowedGen ι 𝔪)
include E


lemma norm_sP_le {𝔥 P : Ideal (𝓞 F)} (hP : P.IsPrime) (he : IsExterior 𝔪 P) (e : ℕ) :
    ‖sP g 𝔥 P e‖ ≤ L2D_betaP (Ideal.absNorm P) e := by
  have := (E.loc g P hP he).Rsum_le (jP 𝔥 P) (Nat.mod_lt _ (by norm_num)) ((e : ℤ) - 2) (by omega)
  have he' : ((e : ℤ) - 2 + 2).toNat = e := by omega
  rw [he'] at this
  exact this

lemma norm_om1_le {P : Ideal (𝓞 F)} (hP : P.IsPrime) (he : IsExterior 𝔪 P) :
    ‖om1 g P‖ ≤ 1 := by
  have := (E.loc g P hP he).Rsum_le 1 (by norm_num) (-2) (by norm_num)
  have h0 : ((-2 : ℤ) + 2).toNat = 0 := by norm_num
  have h1 : L2D_betaP (Ideal.absNorm P : ℝ) 0 = 1 := by simp [L2D_betaP]
  rw [h0, h1] at this
  exact this

lemma norm_mask0_le {P : Ideal (𝓞 F)} (hP : P.IsPrime) (he : IsExterior 𝔪 P) (j : ℕ) :
    ‖mask g P j 0‖ ≤ 1 := (E.loc g P hP he).mask_le j

lemma norm_gaussPhase_le {Q : Ideal (𝓞 F)} (hQ : Q.IsPrime) (he : IsExterior 𝔪 Q) :
    ‖gaussPhase g 2 Q‖ ≤ 1 := (E.loc g Q hQ he).gp_le

omit E in
lemma norm_sext_cases (P : Ideal (𝓞 F)) (x : SInt 𝔪) :
    ‖sexticResidueSymbol ι 𝔪 P x‖ = 0 ∨ ‖sexticResidueSymbol ι 𝔪 P x‖ = 1 := by
  unfold sexticResidueSymbol
  split_ifs with h1 h2
  · left; simp
  · right
    have h6 : (ι (h2.choose : F)) ^ 6 = 1 := by
      rw [← map_pow, ← map_pow]
      have := h2.choose_spec.1
      rw [this]
      simp
    exact Complex.norm_eq_one_of_pow_eq_one h6 (by norm_num)
  · left; simp

omit E in
lemma norm_uSym_cases (P : Ideal (𝓞 F)) (x : F) :
    ‖uSym g P x‖ = 0 ∨ ‖uSym g P x‖ = 1 := by
  unfold uSym localSymbol
  split_ifs with hex
  · rw [norm_mul, Complex.norm_conj]
    rcases norm_sext_cases (ι := ι) P hex.choose.1 with h | h <;>
      rcases norm_sext_cases (ι := ι) P hex.choose.2 with h' | h'
    · left; rw [h, zero_mul]
    · left; rw [h, zero_mul]
    · left; rw [h', mul_zero]
    · right; rw [h, h', one_mul]
  · left; simp

omit E in
lemma norm_uSym_le' (P : Ideal (𝓞 F)) (x : F) : ‖uSym g P x‖ ≤ 1 := by
  rcases norm_uSym_cases g P x with h | h <;> simp [h]

omit E in
lemma norm_uSym_inv_le (P : Ideal (𝓞 F)) (x : F) : ‖(uSym g P x)⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  rcases norm_uSym_cases g P x with h | h <;> simp [h]

lemma norm_prod_le_one' {ι' : Type*} (t : Finset ι') (f : ι' → ℂ) (hf : ∀ i ∈ t, ‖f i‖ ≤ 1) :
    ‖∏ i ∈ t, f i‖ ≤ 1 :=
  (Finset.norm_prod_le _ _).trans (Finset.prod_le_one (fun _ _ => norm_nonneg _) hf)

omit E in
lemma norm_L_eq {χ : HeckeChar F 𝔪} (D : Data χ g) (υ : SClass 𝔪) {I : Ideal (𝓞 F)}
    (hI : IsExterior 𝔪 I) : ‖D.L υ (gF g I)‖ = 1 :=
  D.hLn υ _ (C3B.gen_ne_zero g I hI)

lemma norm_omg_le {χ : HeckeChar F 𝔪} (D : Data χ g) {N : ℕ} (eU : Fin N ≃ SClass 𝔪)
    (υ : SClass 𝔪) (𝔥 𝔣 𝔞 𝔫 : Ideal (𝓞 F)) (s : TT D N) :
    ‖omg g D eU υ 𝔥 𝔣 𝔞 𝔫 s‖ ≤
      ∏ P ∈ prim 𝔣, L2D_betaP (Ideal.absNorm P) (cnt P 𝔞) := by
  unfold omg
  split_ifs with hv
  · obtain ⟨h𝔥, h𝔣, h𝔞, h𝔫, -, -⟩ := hv
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_inv, norm_pow, norm_inv, norm_pow,
      norm_L_eq g D υ h𝔞, norm_L_eq g D υ h𝔫, norm_L_eq g D υ h𝔣]
    have hI : ‖Iin g 𝔥 𝔣‖ ≤ 1 := by
      unfold Iin
      refine norm_prod_le_one' E _ _ fun P hP => ?_
      have hP' := (Finset.mem_sdiff.1 hP).1
      exact norm_mask0_le E g (prime_of_mem_prim hP').1 (exterior_of_prim h𝔥 hP') _
    have hprod : ‖∏ P ∈ prim 𝔣, sP g 𝔥 P (cnt P 𝔞) *
        (uSym g P (urep eU s.1) * uSym g P (gF g 𝔞) * uSym g P (gF g 𝔫) ^ 3 *
          ((uSym g P (gF g 𝔣))⁻¹) ^ 2) ^ bP 𝔥 P (cnt P 𝔞)‖ ≤
        ∏ P ∈ prim 𝔣, L2D_betaP (Ideal.absNorm P) (cnt P 𝔞) := by
      refine (Finset.norm_prod_le _ _).trans (Finset.prod_le_prod (fun _ _ => norm_nonneg _) ?_)
      intro P hP
      rw [norm_mul]
      have h1 := norm_sP_le E g (𝔥 := 𝔥) (prime_of_mem_prim hP).1 (exterior_of_prim h𝔣 hP)
        (cnt P 𝔞)
      have h2 : ‖(uSym g P (urep eU s.1) * uSym g P (gF g 𝔞) * uSym g P (gF g 𝔫) ^ 3 *
          ((uSym g P (gF g 𝔣))⁻¹) ^ 2) ^ bP 𝔥 P (cnt P 𝔞)‖ ≤ 1 := by
        rw [norm_pow]
        refine pow_le_one₀ (norm_nonneg _) ?_
        rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow]
        have a1 := norm_uSym_le' g P (urep eU s.1)
        have a2 := norm_uSym_le' g P (gF g 𝔞)
        have a3 := pow_le_one₀ (n := 3) (norm_nonneg _) (norm_uSym_le' g P (gF g 𝔫))
        have a4 := pow_le_one₀ (n := 2) (norm_nonneg _) (norm_uSym_inv_le g P (gF g 𝔣))
        exact mul_le_one₀ (mul_le_one₀ (mul_le_one₀ a1 (norm_nonneg _) a2) (by positivity) a3)
          (by positivity) a4
      calc ‖sP g 𝔥 P (cnt P 𝔞)‖ * _ ≤ L2D_betaP (Ideal.absNorm P) (cnt P 𝔞) * 1 :=
            mul_le_mul h1 h2 (norm_nonneg _) (L2D_betaP_nonneg _ (Nat.cast_nonneg _) _)
        _ = _ := mul_one _
    calc ‖Iin g 𝔥 𝔣‖ * 1⁻¹ * 1⁻¹ ^ 3 * 1 ^ 2 * _ ≤ 1 * 1⁻¹ * 1⁻¹ ^ 3 * 1 ^ 2 *
          ∏ P ∈ prim 𝔣, L2D_betaP (Ideal.absNorm P) (cnt P 𝔞) := by
          gcongr
      _ = _ := by simp
  · rw [norm_zero]
    exact Finset.prod_nonneg fun _ _ => L2D_betaP_nonneg _ (Nat.cast_nonneg _) _

omit E in
lemma omg_eq_zero {χ : HeckeChar F 𝔪} (D : Data χ g) {N : ℕ} (eU : Fin N ≃ SClass 𝔪)
    (υ : SClass 𝔪) (𝔥 𝔣 𝔞 𝔫 : Ideal (𝓞 F)) (s : TT D N)
    (h : ∃ P ∈ normalizedFactors 𝔞, ¬ P ∣ 𝔣) : omg g D eU υ 𝔥 𝔣 𝔞 𝔫 s = 0 := by
  unfold omg
  rw [if_neg]
  rintro ⟨-, -, -, -, h1, -⟩
  obtain ⟨P, hP, hP'⟩ := h
  exact hP' (h1 P hP)

lemma norm_rho_le {χ : HeckeChar F 𝔪} (D : Data χ g) {N : ℕ} (eU : Fin N ≃ SClass 𝔪)
    (υ : SClass 𝔪) (𝔥 𝔣 𝔞 𝔫 : Ideal (𝓞 F)) (s : TT D N) (𝔡 : Ideal (𝓞 F)) :
    ‖rho g D eU υ 𝔥 𝔣 𝔞 𝔫 s 𝔡‖ ≤ 1 := by
  unfold rho
  split_ifs with hv
  · obtain ⟨h𝔡, -, -⟩ := hv
    rw [norm_mul, norm_mul, norm_pow, norm_L_eq g D υ h𝔡, one_pow, one_mul]
    refine mul_le_one₀ ?_ (norm_nonneg _) ?_
    · refine norm_prod_le_one' E _ _ fun P hP => ?_
      rw [norm_mul, norm_pow]
      refine mul_le_one₀ (norm_om1_le E g (prime_of_mem_prim hP).1 (exterior_of_prim h𝔡 hP))
        (by positivity) (pow_le_one₀ (norm_nonneg _) ?_)
      rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow]
      have a1 := norm_uSym_le' g P (urep eU s.1)
      have a2 := norm_uSym_le' g P (gF g 𝔞)
      have a3 := pow_le_one₀ (n := 3) (norm_nonneg _) (norm_uSym_le' g P (gF g 𝔫))
      have a4 := pow_le_one₀ (n := 2) (norm_nonneg _) (norm_uSym_inv_le g P (gF g 𝔡))
      have a5 := pow_le_one₀ (n := 2) (norm_nonneg _) (norm_uSym_inv_le g P (gF g 𝔣))
      exact mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (mul_le_one₀ a1 (norm_nonneg _) a2)
        (by positivity) a3) (by positivity) a4) (by positivity) a5
    · refine norm_prod_le_one' E _ _ fun P _ => ?_
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (norm_uSym_inv_le g P (gF g 𝔡))
  · rw [norm_zero]; exact zero_le_one

lemma norm_lam_le {χ : HeckeChar F 𝔪} (D : Data χ g) {N : ℕ} (eU : Fin N ≃ SClass 𝔪)
    (υ : SClass 𝔪) (𝔥 𝔣 𝔞 𝔫 : Ideal (𝓞 F)) (s : TT D N) (𝔠 : Ideal (𝓞 F)) :
    ‖lam g D eU υ 𝔥 𝔣 𝔞 𝔫 s 𝔠‖ ≤ 1 := by
  unfold lam
  split_ifs with hv
  · obtain ⟨h𝔠, -, -⟩ := hv
    rw [norm_mul, norm_mul, norm_inv, norm_L_eq g D υ h𝔠, inv_one, one_mul]
    refine mul_le_one₀ ?_ (norm_nonneg _) ?_
    · refine norm_prod_le_one' E _ _ fun P _ => ?_
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (norm_uSym_le' g P (gF g 𝔠))
    · refine norm_prod_le_one' E _ _ fun Q hQ => ?_
      rw [norm_mul, norm_pow]
      refine mul_le_one₀ (norm_gaussPhase_le E g (prime_of_mem_prim hQ).1 (exterior_of_prim h𝔠 hQ))
        (by positivity) (pow_le_one₀ (norm_nonneg _) ?_)
      rw [norm_mul, norm_mul, norm_mul, norm_pow]
      have a1 := norm_uSym_le' g Q (urep eU s.1)
      have a2 := norm_uSym_le' g Q (gF g 𝔞)
      have a3 := norm_uSym_le' g Q (gF g 𝔠)
      have a4 := pow_le_one₀ (n := 2) (norm_nonneg _) (norm_uSym_inv_le g Q (gF g 𝔣))
      exact mul_le_one₀ (mul_le_one₀ (mul_le_one₀ a1 (norm_nonneg _) a2) (by positivity) a3)
        (by positivity) a4
  · rw [norm_zero]; exact zero_le_one

end env

end L3V

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3V_Exp: expanding the exterior product over the active sets `𝔣 ∈ 𝓕(𝔥)`

For a row `r = (𝔟, υ)` with `𝔟 = 𝔥 𝔡`, `𝔡 = simplePart 𝔟`, the product `∏_P E_P(ν)` is
`∑_{A ⊆ prim 𝔥} E_A(ν)`, where at `P ∈ A` the nonzero digits are taken, at `P ∈ prim 𝔥 ∖ A` the
zero digit, at `P ∣ 𝔡` (where `j = 1`, so `α(0) = 0`) the nonzero digits, and `W_P(a(ν))` elsewhere.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-- The local argument `t = ν p^{−e₀}` of the cut. -/
noncomputable def tz (g : AllowedGen ι 𝔪) (r z : RowClass 𝔪) (P : Ideal (𝓞 F)) : F :=
  nu g r z * (g.gen P : F) ^ (-(e0 r z P))

/-- The `A`-part `E_A(ν)` of the exterior product. -/
noncomputable def EA (g : AllowedGen ι 𝔪) (r z : RowClass 𝔪) (𝔥 : Ideal (𝓞 F))
    (A : Finset (Ideal (𝓞 F))) : ℂ :=
  (∏ P ∈ A, Rsum g P (cnt P r.1.1 % 6) (e0 r z P) (tz g r z P)) *
    (∏ P ∈ prim 𝔥 \ A, mask g P (cnt P r.1.1 % 6) 0 * Wsph g P (e0 r z P) (tz g r z P)) *
    (∏ P ∈ prim (simplePart r.1.1), Rsum g P 1 (e0 r z P) (tz g r z P)) *
    ∏ P ∈ prim (z.1.1 * r.1.1) \ prim r.1.1, Wsph g P (e0 r z P) (tz g r z P)

lemma prim_mul {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) : prim (I * J) = prim I ∪ prim J := by
  classical
  unfold prim
  rw [normalizedFactors_mul hI hJ, Multiset.toFinset_add]

lemma cnt_simplePart {𝔟 P : Ideal (𝓞 F)} (h𝔟 : 𝔟 ≠ ⊥) :
    cnt P (simplePart 𝔟) = if cnt P 𝔟 = 1 then 1 else 0 := by
  classical
  unfold cnt
  rw [L2D_simplePart_nf]
  by_cases h1 : (normalizedFactors 𝔟).count P = 1
  · rw [if_pos h1]
    apply Multiset.count_eq_one_of_mem (Finset.nodup _)
    rw [Finset.mem_val, Finset.mem_filter, Multiset.mem_toFinset]
    exact ⟨Multiset.one_le_count_iff_mem.1 (by omega), h1⟩
  · rw [if_neg h1]
    apply Multiset.count_eq_zero_of_notMem
    rw [Finset.mem_val, Finset.mem_filter]; tauto

/-- `𝔟 = 𝔥 𝔡`: exponents. -/
lemma cnt_row {𝔟 𝔥 P : Ideal (𝓞 F)} (h𝔟 : 𝔟 ≠ ⊥) (h𝔥 : 𝔥 * simplePart 𝔟 = 𝔟) :
    cnt P 𝔟 = cnt P 𝔥 + cnt P (simplePart 𝔟) := by
  have hh0 : 𝔥 ≠ ⊥ := by rintro rfl; apply h𝔟; rw [← h𝔥]; simp
  conv_lhs => rw [← h𝔥]
  rw [cnt_mul hh0 (L2D_simplePart_ne_bot 𝔟 h𝔟)]

lemma cnt_h_of_mem {𝔟 𝔥 P : Ideal (𝓞 F)} (h𝔟 : 𝔟 ≠ ⊥) (h𝔥 : 𝔥 * simplePart 𝔟 = 𝔟)
    (hP : P ∈ prim 𝔥) : 2 ≤ cnt P 𝔥 ∧ cnt P (simplePart 𝔟) = 0 ∧ cnt P 𝔟 = cnt P 𝔥 := by
  have hpow := L2D_powerful_of_mul 𝔟 𝔥 h𝔟 h𝔥
  have h2 : 2 ≤ cnt P 𝔥 := hpow.2 P (Multiset.mem_toFinset.1 hP)
  have hr := cnt_row (P := P) h𝔟 h𝔥
  rw [cnt_simplePart h𝔟] at hr ⊢
  refine ⟨h2, ?_, ?_⟩
  · rw [if_neg (by omega)]
  · rw [if_neg (by omega)] at hr; omega

lemma cnt_d_of_mem {𝔟 𝔥 P : Ideal (𝓞 F)} (h𝔟 : 𝔟 ≠ ⊥) (h𝔥 : 𝔥 * simplePart 𝔟 = 𝔟)
    (hP : P ∈ prim (simplePart 𝔟)) : cnt P 𝔥 = 0 ∧ cnt P 𝔟 = 1 := by
  have hc := mem_prim_iff.1 hP
  rw [cnt_simplePart h𝔟] at hc
  have h1 : cnt P 𝔟 = 1 := by by_contra h; rw [if_neg h] at hc; omega
  have hr := cnt_row (P := P) h𝔟 h𝔥
  rw [cnt_simplePart h𝔟, if_pos h1] at hr
  exact ⟨by omega, h1⟩

lemma prim_row {𝔟 𝔥 : Ideal (𝓞 F)} (h𝔟 : 𝔟 ≠ ⊥) (h𝔥 : 𝔥 * simplePart 𝔟 = 𝔟) :
    prim 𝔟 = prim 𝔥 ∪ prim (simplePart 𝔟) ∧ Disjoint (prim 𝔥) (prim (simplePart 𝔟)) := by
  have hh0 : 𝔥 ≠ ⊥ := by rintro rfl; apply h𝔟; rw [← h𝔥]; simp
  refine ⟨?_, ?_⟩
  · conv_lhs => rw [← h𝔥]
    exact prim_mul hh0 (L2D_simplePart_ne_bot 𝔟 h𝔟)
  · rw [Finset.disjoint_left]
    intro P hP hP'
    have := (cnt_h_of_mem h𝔟 h𝔥 hP).2.1
    have := mem_prim_iff.1 hP'
    omega

variable (E : Env ι 𝔪) (g : AllowedGen ι 𝔪)
include E

/-- `∏_P E_P(ν) = ∑_{A ⊆ prim 𝔥} E_A(ν)`. -/
lemma Eprod_expand (r : RowClass 𝔪) {𝔥 : Ideal (𝓞 F)} (h𝔥 : 𝔥 * simplePart r.1.1 = r.1.1)
    (z : RowClass 𝔪) :
    Eprod g r z = ∑ A ∈ (prim 𝔥).powerset, EA g r z 𝔥 A := by
  classical
  have h𝔟 : r.1.1 ≠ ⊥ := r.1.2.1
  have hz : z.1.1 ≠ ⊥ := z.1.2.1
  obtain ⟨hrow, hdisj⟩ := prim_row h𝔟 h𝔥
  have hsub : prim r.1.1 ⊆ prim (z.1.1 * r.1.1) := by
    rw [prim_mul hz h𝔟]; exact Finset.subset_union_right
  unfold Eprod
  -- the local factors
  have hgood : ∀ P ∈ prim r.1.1, ∃ hP : P.IsPrime, IsExterior 𝔪 P := fun P hP =>
    ⟨(prime_of_mem_prim hP).1, exterior_of_prim r.1.2 hP⟩
  have hH : ∀ P ∈ prim 𝔥, Eloc g P ((normalizedFactors r.1.1).count P) (e0 r z P) (tz g r z P) =
      Rsum g P (cnt P r.1.1 % 6) (e0 r z P) (tz g r z P) +
        mask g P (cnt P r.1.1 % 6) 0 * Wsph g P (e0 r z P) (tz g r z P) := by
    intro P hP
    obtain ⟨hPp, hPe⟩ := hgood P (hrow ▸ Finset.mem_union_left _ hP)
    have hk : (normalizedFactors r.1.1).count P ≠ 0 := by
      have := (cnt_h_of_mem h𝔟 h𝔥 hP).1
      have := (cnt_h_of_mem h𝔟 h𝔥 hP).2.2
      change cnt P r.1.1 ≠ 0; omega
    rw [(E.loc g P hPp hPe).Eloc_split _ hk, add_comm]
  have hD : ∀ P ∈ prim (simplePart r.1.1),
      Eloc g P ((normalizedFactors r.1.1).count P) (e0 r z P) (tz g r z P) =
        Rsum g P 1 (e0 r z P) (tz g r z P) := by
    intro P hP
    obtain ⟨hPp, hPe⟩ := hgood P (hrow ▸ Finset.mem_union_right _ hP)
    have h1 := (cnt_d_of_mem h𝔟 h𝔥 hP).2
    have hk : (normalizedFactors r.1.1).count P ≠ 0 := by change cnt P r.1.1 ≠ 0; omega
    have h16 : (normalizedFactors r.1.1).count P % 6 = 1 := by change cnt P r.1.1 % 6 = 1; omega
    rw [(E.loc g P hPp hPe).Eloc_split _ hk, h16,
      (E.loc g P hPp hPe).mask_zero 1 one_ne_zero, zero_mul, zero_add]
  have hX : ∀ P ∈ prim (z.1.1 * r.1.1) \ prim r.1.1,
      Eloc g P ((normalizedFactors r.1.1).count P) (e0 r z P) (tz g r z P) =
        Wsph g P (e0 r z P) (tz g r z P) := by
    intro P hP
    have h0 : (normalizedFactors r.1.1).count P = 0 := by
      have := (Finset.mem_sdiff.1 hP).2
      rw [mem_prim_iff] at this; change ¬ 0 < cnt P r.1.1 at this; change cnt P r.1.1 = 0; omega
    unfold Eloc; rw [if_pos h0]
  have hsplit : ∏ P ∈ prim r.1.1,
      Eloc g P ((normalizedFactors r.1.1).count P) (e0 r z P) (tz g r z P) =
      (∏ P ∈ prim 𝔥, Eloc g P ((normalizedFactors r.1.1).count P) (e0 r z P) (tz g r z P)) *
        ∏ P ∈ prim (simplePart r.1.1),
          Eloc g P ((normalizedFactors r.1.1).count P) (e0 r z P) (tz g r z P) := by
    rw [hrow, Finset.prod_union hdisj]
  have htz : ∀ P, nu g r z * (g.gen P : F) ^ (-(e0 r z P)) = tz g r z P := fun P => rfl
  simp only [htz]
  rw [← Finset.prod_sdiff hsub, hsplit, Finset.prod_congr rfl hX, Finset.prod_congr rfl hH,
    Finset.prod_congr rfl hD, Finset.prod_add, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  unfold EA
  ring

end L3V

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3V_Eval1: the reflected frequency of a key, its exponents and unit parts

For a key `(𝔣, 𝔞', 𝔫', u, 𝔠')` with `𝔥 = 𝔣 𝔤` the frequency is `x = ε_u gen(𝔤² 𝔞' 𝔠' 𝔫'³)`,
`ν = x / b²` (6.21). `KeyHyp` collects the support conditions; `cnt_x`, `e0_eq` compute
`v_P(ν) = v_P(𝔞') + v_P(𝔠') + 3 v_P(𝔫') − 2 v_P(𝔣) − 2 v_P(𝔡)`; `e0_eq_vP`: it is `vP P ν`, so the
cut's local argument is the unit part of `ν`; `Rsum_tz`, `Wsph_tz` evaluate the local factors with
`U_P = uSym_P(ν)`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-- The support conditions of a key, for the row `r` and powerful part `𝔥 = 𝔣 𝔤`. -/
structure KeyHyp (r : RowClass 𝔪) (𝔥 𝔣 𝔤 𝔞 𝔫 𝔠 : Ideal (𝓞 F)) : Prop where
  h𝔥 : 𝔥 * simplePart r.1.1 = r.1.1
  hfg : 𝔥 = 𝔣 * 𝔤
  hsf : Squarefree 𝔣
  hff : 𝔣 * 𝔣 ∣ 𝔥
  ha : IsExterior 𝔪 𝔞
  haf : ∀ P ∈ normalizedFactors 𝔞, P ∣ 𝔣
  hn : IsExterior 𝔪 𝔫
  hnf : 𝔫 ⊔ 𝔣 = ⊤
  hdn : simplePart r.1.1 ⊔ 𝔫 = ⊤
  hc : IsExterior 𝔪 𝔠
  hcs : Squarefree 𝔠
  hcf : 𝔠 ⊔ 𝔣 = ⊤
  hcd : 𝔠 ⊔ simplePart r.1.1 = ⊤

/-- The frequency ideal `𝔵 = 𝔤² 𝔞' 𝔠' 𝔫'³`. -/
def xI (𝔤 𝔞 𝔫 𝔠 : Ideal (𝓞 F)) : Ideal (𝓞 F) := 𝔤 ^ 2 * 𝔞 * 𝔠 * 𝔫 ^ 3

namespace KeyHyp

variable {r : RowClass 𝔪} {𝔥 𝔣 𝔤 𝔞 𝔫 𝔠 : Ideal (𝓞 F)} (K : KeyHyp r 𝔥 𝔣 𝔤 𝔞 𝔫 𝔠)
include K

lemma b_ne : r.1.1 ≠ ⊥ := r.1.2.1

lemma h_ext : IsExterior 𝔪 𝔥 := C3M.isExterior_of_mul_left (K.h𝔥.symm ▸ r.1.2)

lemma d_ext : IsExterior 𝔪 (simplePart r.1.1) := C3M.isExterior_of_mul_right (K.h𝔥.symm ▸ r.1.2)

lemma f_ext : IsExterior 𝔪 𝔣 := C3M.isExterior_of_mul_left (K.hfg ▸ K.h_ext)

lemma g_ext : IsExterior 𝔪 𝔤 := C3M.isExterior_of_mul_right (K.hfg ▸ K.h_ext)

lemma x_ext : IsExterior 𝔪 (xI 𝔤 𝔞 𝔫 𝔠) := by
  unfold xI
  exact C3I.isExterior_mul (C3I.isExterior_mul (C3I.isExterior_mul
    (C3I.isExterior_pow K.g_ext 2) K.ha) K.hc) (C3I.isExterior_pow K.hn 3)

lemma cnt_x (P : Ideal (𝓞 F)) :
    cnt P (xI 𝔤 𝔞 𝔫 𝔠) = 2 * cnt P 𝔤 + cnt P 𝔞 + cnt P 𝔠 + 3 * cnt P 𝔫 := by
  unfold xI
  have hg := K.g_ext.1; have ha := K.ha.1; have hc := K.hc.1; have hn := K.hn.1
  rw [cnt_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hg) ha) hc) (pow_ne_zero _ hn),
    cnt_mul (mul_ne_zero (pow_ne_zero _ hg) ha) hc, cnt_mul (pow_ne_zero _ hg) ha, cnt_pow, cnt_pow]

lemma cnt_b (P : Ideal (𝓞 F)) :
    cnt P r.1.1 = cnt P 𝔣 + cnt P 𝔤 + cnt P (simplePart r.1.1) := by
  rw [cnt_row K.b_ne K.h𝔥, K.hfg, cnt_mul K.f_ext.1 K.g_ext.1]

lemma cop_cnt {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (h : I ⊔ J = ⊤) (P : Ideal (𝓞 F)) :
    cnt P I = 0 ∨ cnt P J = 0 := (sup_eq_top_iff_cnt hI hJ).1 h P

lemma cnt_f_le (P : Ideal (𝓞 F)) : cnt P 𝔣 ≤ 1 := (squarefree_iff_cnt K.f_ext.1).1 K.hsf P

lemma cnt_c_le (P : Ideal (𝓞 F)) : cnt P 𝔠 ≤ 1 := (squarefree_iff_cnt K.hc.1).1 K.hcs P

lemma cnt_g_of_f {P : Ideal (𝓞 F)} (hP : cnt P 𝔣 = 1) : 1 ≤ cnt P 𝔤 := by
  have hd : 𝔣 * 𝔣 ∣ 𝔣 * 𝔤 := K.hfg ▸ K.hff
  have hfg : 𝔣 ∣ 𝔤 := (mul_dvd_mul_iff_left K.f_ext.1).1 hd
  have hle := (dvd_iff_normalizedFactors_le_normalizedFactors K.f_ext.1 K.g_ext.1).1 hfg
  have := Multiset.count_le_of_le P hle
  change cnt P 𝔣 ≤ cnt P 𝔤 at this
  omega

lemma cnt_a_of {P : Ideal (𝓞 F)} (hP : cnt P 𝔣 = 0) : cnt P 𝔞 = 0 := by
  by_contra h
  have hm : P ∈ normalizedFactors 𝔞 := Multiset.count_ne_zero.1 h
  have hpf := K.haf P hm
  have hp := L2D_prime_of_mem hm
  have := (dvd_iff_cnt_pos (Ideal.isPrime_of_prime hp) hp.ne_zero K.f_ext.1).1 hpf
  omega

lemma cnt_hd (P : Ideal (𝓞 F)) : cnt P 𝔥 = 0 ∨ cnt P (simplePart r.1.1) = 0 := by
  by_cases hP : P ∈ prim 𝔥
  · right; exact (cnt_h_of_mem K.b_ne K.h𝔥 hP).2.1
  · left; rw [mem_prim_iff] at hP; omega

lemma cnt_h (P : Ideal (𝓞 F)) : cnt P 𝔥 = cnt P 𝔣 + cnt P 𝔤 := by
  rw [K.hfg, cnt_mul K.f_ext.1 K.g_ext.1]

/-- `v_P(ν)` for the key's frequency. -/
lemma e0_val (P : Ideal (𝓞 F)) (u : SClass 𝔪) :
    e0 r (⟨xI 𝔤 𝔞 𝔫 𝔠, K.x_ext⟩, u) P = (cnt P 𝔞 : ℤ) + (cnt P 𝔠 + 3 * cnt P 𝔫 : ℕ) -
      2 * (cnt P 𝔣 : ℤ) - 2 * (cnt P (simplePart r.1.1) : ℤ) := by
  unfold e0
  change ((cnt P (xI 𝔤 𝔞 𝔫 𝔠) : ℕ) : ℤ) - 2 * ((cnt P r.1.1 : ℕ) : ℤ) = _
  rw [K.cnt_x, K.cnt_b]
  push_cast; ring

end KeyHyp

/-! ### `ν` and its unit parts -/

section nu

variable (E : Env ι 𝔪) (g : AllowedGen ι 𝔪)

lemma rep_ne_zero (u : SClass 𝔪) : ((u.rep : SInt 𝔪) : F) ≠ 0 := by
  intro h0
  have : (u.rep : SInt 𝔪) = 0 := Subtype.ext h0
  have hu : IsUnit (u.rep : SInt 𝔪) := by
    unfold SClass.rep; exact Units.isUnit _
  rw [this] at hu
  exact not_isUnit_zero hu

include E in
lemma vP_nu {P : Ideal (𝓞 F)} (hP : P.IsPrime) (he : IsExterior 𝔪 P) (r z : RowClass 𝔪) :
    vP P (nu g r z) = e0 r z P := by
  set v : HeightOneSpectrum (𝓞 F) := ⟨P, hP, he.1⟩
  have hrep : vP v.asIdeal ((z.2.rep : SInt 𝔪) : F) = 0 := by
    unfold SClass.rep; exact vP_unitE hP he _
  have hx := C3B.gen_ne_zero g z.1.1 z.1.2
  have hb := C3B.gen_ne_zero g r.1.1 r.1.2
  have hr := rep_ne_zero z.2
  change vP v.asIdeal _ = _
  unfold nu rowElt e0
  rw [Subalgebra.coe_mul, div_eq_mul_inv, vP_mul (mul_ne_zero hr hx) (inv_ne_zero (pow_ne_zero _ hb)),
    vP_mul hr hx, vP_inv, pow_two, vP_mul hb hb, hrep, vP_genE E g hP he _ z.1.2, vP_genE E g hP he _ r.1.2]
  ring

lemma tz_eq (r z : RowClass 𝔪) (P : Ideal (𝓞 F)) (h : vP P (nu g r z) = e0 r z P) :
    tz g r z P = nu g r z * (g.gen P : F) ^ (-(vP P (nu g r z))) := by
  unfold tz; rw [h]

lemma nu_ne_zero (r z : RowClass 𝔪) : nu g r z ≠ 0 := by
  unfold nu rowElt
  rw [Subalgebra.coe_mul]
  exact div_ne_zero (mul_ne_zero (rep_ne_zero z.2) (C3B.gen_ne_zero g z.1.1 z.1.2))
    (pow_ne_zero _ (C3B.gen_ne_zero g r.1.1 r.1.2))

include E in
lemma localSymbol_tz {P : Ideal (𝓞 F)} (hP : P.IsPrime) (he : IsExterior 𝔪 P) (r z : RowClass 𝔪) :
    localSymbol ι 𝔪 P (tz g r z P) = uSym g P (nu g r z) := by
  rw [tz_eq g r z P (vP_nu E g hP he r z)]; rfl

include E in
lemma Wsph_tz {P : Ideal (𝓞 F)} (hP : P.IsPrime) (he : IsExterior 𝔪 P) (r z : RowClass 𝔪)
    (n : ℕ) (hn : e0 r z P = n) :
    Wsph g P (e0 r z P) (tz g r z P) = uSym g P (nu g r z) ^ (2 * n) * Wv g P n := by
  unfold Wsph
  rw [if_neg (by omega), localSymbol_tz E g hP he, hn]
  simp

include E in
lemma Rsum_tz {P : Ideal (𝓞 F)} (hP : P.IsPrime) (he : IsExterior 𝔪 P) (r z : RowClass 𝔪)
    {j : ℕ} (hj : j < 6) (he0 : 0 ≤ e0 r z P + 2) :
    Rsum g P j (e0 r z P) (tz g r z P) =
      Rsum g P j (e0 r z P) 1 * uSym g P (nu g r z) ^ bexp j (e0 r z P + 2).toNat := by
  have hval : (⟨P, hP, he.1⟩ : HeightOneSpectrum (𝓞 F)).valuation F (tz g r z P) = 1 := by
    rw [tz_eq g r z P (vP_nu E g hP he r z)]
    exact val_unitPartE E g hP he (nu_ne_zero g r z)
  have h1 := (E.loc g P hP he).Rsum_mono j hj _ he0 _ hval
  rw [localSymbol_tz E g hP he] at h1
  exact h1

end nu

end L3V

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3V_Eval2: the exterior factor `E_t(𝔡, 𝔠′)` of (6.27) at a key, in unit-part symbols

`EA_eval`: for the key's frequency `ν`, with `U_P = uSym_P(ν)` and `y_Q = v_Q(𝔠′) + 3 v_Q(𝔫′)`,
`E_{prim 𝔣}(ν) = (∏_{𝔭∣𝔣} s_𝔭 U_𝔭^{b_𝔭}) · I_{𝔥,𝔣} · ∏_{𝔮 ∣ 𝔠′𝔫′} U_𝔮^{2y} W_{y} · ∏_{𝔭∣𝔡} ω_𝔭 U_𝔭^{13}`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

variable (E : Env ι 𝔪) (g : AllowedGen ι 𝔪) {r : RowClass 𝔪} {𝔥 𝔣 𝔤 𝔞 𝔫 𝔠 : Ideal (𝓞 F)}
  (K : KeyHyp r 𝔥 𝔣 𝔤 𝔞 𝔫 𝔠) (u : SClass 𝔪)
include E K

/-- The key's frequency class. -/
abbrev zK : RowClass 𝔪 := (⟨xI 𝔤 𝔞 𝔫 𝔠, K.x_ext⟩, u)

omit E in
lemma mem_f_facts {P : Ideal (𝓞 F)} (hP : P ∈ prim 𝔣) :
    cnt P 𝔣 = 1 ∧ cnt P (simplePart r.1.1) = 0 ∧ cnt P 𝔠 = 0 ∧ cnt P 𝔫 = 0 ∧
      cnt P r.1.1 = cnt P 𝔥 := by
  have h1 : cnt P 𝔣 = 1 := le_antisymm (K.cnt_f_le P) (mem_prim_iff.1 hP)
  have hg := K.cnt_g_of_f h1
  have hh : cnt P 𝔥 ≠ 0 := by rw [K.cnt_h]; omega
  have hd : cnt P (simplePart r.1.1) = 0 := by rcases K.cnt_hd P with h | h <;> [omega; exact h]
  have hc : cnt P 𝔠 = 0 := by
    rcases K.cop_cnt K.hc.1 K.f_ext.1 K.hcf P with h | h <;> [exact h; omega]
  have hn : cnt P 𝔫 = 0 := by
    rcases K.cop_cnt K.hn.1 K.f_ext.1 K.hnf P with h | h <;> [exact h; omega]
  refine ⟨h1, hd, hc, hn, ?_⟩
  rw [K.cnt_b, hd, K.cnt_h]; ring

omit E in
lemma mem_h_not_f_facts {P : Ideal (𝓞 F)} (hP : P ∈ prim 𝔥 \ prim 𝔣) :
    cnt P 𝔣 = 0 ∧ cnt P 𝔞 = 0 ∧ cnt P (simplePart r.1.1) = 0 ∧ cnt P r.1.1 = cnt P 𝔥 := by
  have h0 : cnt P 𝔣 = 0 := by
    have := (Finset.mem_sdiff.1 hP).2; rw [mem_prim_iff] at this; omega
  have hd := (cnt_h_of_mem K.b_ne K.h𝔥 (Finset.mem_sdiff.1 hP).1).2.1
  refine ⟨h0, K.cnt_a_of h0, hd, ?_⟩
  rw [K.cnt_b, hd, K.cnt_h]; ring

omit E in
lemma mem_d_facts {P : Ideal (𝓞 F)} (hP : P ∈ prim (simplePart r.1.1)) :
    cnt P 𝔣 = 0 ∧ cnt P 𝔞 = 0 ∧ cnt P (simplePart r.1.1) = 1 ∧ cnt P 𝔠 = 0 ∧ cnt P 𝔫 = 0 := by
  have hd := cnt_d_of_mem K.b_ne K.h𝔥 hP
  have hd1 : cnt P (simplePart r.1.1) = 1 := by
    have := cnt_row (P := P) K.b_ne K.h𝔥; omega
  have hf : cnt P 𝔣 = 0 := by have := K.cnt_h P; omega
  have hc : cnt P 𝔠 = 0 := by
    rcases K.cop_cnt K.hc.1 K.d_ext.1 K.hcd P with h | h <;> [exact h; omega]
  have hn : cnt P 𝔫 = 0 := by
    rcases K.cop_cnt K.d_ext.1 K.hn.1 K.hdn P with h | h <;> [omega; exact h]
  exact ⟨hf, K.cnt_a_of hf, hd1, hc, hn⟩

omit E in
lemma mem_out_facts {P : Ideal (𝓞 F)} (hP : P ∉ prim r.1.1) :
    cnt P 𝔣 = 0 ∧ cnt P 𝔞 = 0 ∧ cnt P (simplePart r.1.1) = 0 := by
  rw [mem_prim_iff] at hP
  have := K.cnt_b P
  have hf : cnt P 𝔣 = 0 := by omega
  exact ⟨hf, K.cnt_a_of hf, by omega⟩

/-- The `W`-part `φ_Q = U_Q^{2y} W_y`. -/
noncomputable def phiW (z : RowClass 𝔪) (𝔫 𝔠 Q : Ideal (𝓞 F)) : ℂ :=
  uSym g Q (nu g r z) ^ (2 * (cnt Q 𝔠 + 3 * cnt Q 𝔫)) * Wv g Q (cnt Q 𝔠 + 3 * cnt Q 𝔫)

lemma EA_eval :
    EA g r (zK K u) 𝔥 (prim 𝔣) =
      (∏ P ∈ prim 𝔣, sP g 𝔥 P (cnt P 𝔞) * uSym g P (nu g r (zK K u)) ^ bP 𝔥 P (cnt P 𝔞)) *
        Iin g 𝔥 𝔣 * (∏ Q ∈ prim (𝔠 * 𝔫), phiW g (r := r) (zK K u) 𝔫 𝔠 Q) *
        ∏ P ∈ prim (simplePart r.1.1), om1 g P * uSym g P (nu g r (zK K u)) ^ 13 := by
  classical
  set z := zK K u with hz
  have hprimP : ∀ {P I : Ideal (𝓞 F)}, P ∈ prim I → IsExterior 𝔪 I → P.IsPrime ∧ IsExterior 𝔪 P :=
    fun hP hI => ⟨(prime_of_mem_prim hP).1, exterior_of_prim hI hP⟩
  -- (a) active primes
  have hA : ∀ P ∈ prim 𝔣, Rsum g P (cnt P r.1.1 % 6) (e0 r z P) (tz g r z P) =
      sP g 𝔥 P (cnt P 𝔞) * uSym g P (nu g r z) ^ bP 𝔥 P (cnt P 𝔞) := by
    intro P hP
    obtain ⟨hf1, hd0, hc0, hn0, hb⟩ := mem_f_facts K hP
    obtain ⟨hPp, hPe⟩ := hprimP hP K.f_ext
    have he : e0 r z P = (cnt P 𝔞 : ℤ) - 2 := by
      rw [hz, K.e0_val P u, hf1, hd0, hc0, hn0]; push_cast; ring
    have ht : ((cnt P 𝔞 : ℤ) - 2 + 2).toNat = cnt P 𝔞 := by omega
    rw [Rsum_tz E g hPp hPe r z (Nat.mod_lt _ (by norm_num)) (by omega), he, hb, ht]
    rfl
  -- (b) inactive primes of `𝔥`
  have hB : ∀ P ∈ prim 𝔥 \ prim 𝔣,
      mask g P (cnt P r.1.1 % 6) 0 * Wsph g P (e0 r z P) (tz g r z P) =
        mask g P (jP 𝔥 P) 0 * phiW g (r := r) z 𝔫 𝔠 P := by
    intro P hP
    obtain ⟨hf0, ha0, hd0, hb⟩ := mem_h_not_f_facts K hP
    obtain ⟨hPp, hPe⟩ := hprimP (Finset.mem_sdiff.1 hP).1 K.h_ext
    have he : e0 r z P = ((cnt P 𝔠 + 3 * cnt P 𝔫 : ℕ) : ℤ) := by
      rw [hz, K.e0_val P u, hf0, ha0, hd0]; push_cast; ring
    rw [Wsph_tz E g hPp hPe r z _ he, hb]
    rfl
  -- (c) primes of `𝔡`
  have hC : ∀ P ∈ prim (simplePart r.1.1), Rsum g P 1 (e0 r z P) (tz g r z P) =
      om1 g P * uSym g P (nu g r z) ^ 13 := by
    intro P hP
    obtain ⟨hf0, ha0, hd1, hc0, hn0⟩ := mem_d_facts K hP
    obtain ⟨hPp, hPe⟩ := hprimP hP K.d_ext
    have he : e0 r z P = -2 := by
      rw [hz, K.e0_val P u, hf0, ha0, hd1, hc0, hn0]; push_cast
    rw [Rsum_tz E g hPp hPe r z (by norm_num) (by omega), he]
    rfl
  -- (d) the remaining primes
  have hD : ∀ P ∈ prim (z.1.1 * r.1.1) \ prim r.1.1, Wsph g P (e0 r z P) (tz g r z P) =
      phiW g (r := r) z 𝔫 𝔠 P := by
    intro P hP
    obtain ⟨hf0, ha0, hd0⟩ := mem_out_facts K (Finset.mem_sdiff.1 hP).2
    have hzb : IsExterior 𝔪 (z.1.1 * r.1.1) := C3I.isExterior_mul z.1.2 r.1.2
    obtain ⟨hPp, hPe⟩ := hprimP (Finset.mem_sdiff.1 hP).1 hzb
    have he : e0 r z P = ((cnt P 𝔠 + 3 * cnt P 𝔫 : ℕ) : ℤ) := by
      rw [hz, K.e0_val P u, hf0, ha0, hd0]; push_cast; ring
    rw [Wsph_tz E g hPp hPe r z _ he]
    rfl
  unfold EA
  rw [Finset.prod_congr rfl hA, Finset.prod_congr rfl hB, Finset.prod_congr rfl hC,
    Finset.prod_congr rfl hD, Finset.prod_mul_distrib]
  -- (e) the `W`-parts combine over the primes of `𝔠′ 𝔫′`
  have hdisj : Disjoint (prim 𝔥 \ prim 𝔣) (prim (z.1.1 * r.1.1) \ prim r.1.1) := by
    rw [Finset.disjoint_left]
    intro P hP hP'
    apply (Finset.mem_sdiff.1 hP').2
    rw [(prim_row K.b_ne K.h𝔥).1]
    exact Finset.mem_union_left _ (Finset.mem_sdiff.1 hP).1
  have hcn : 𝔠 * 𝔫 ≠ ⊥ := mul_ne_zero K.hc.1 K.hn.1
  have hsub : prim (𝔠 * 𝔫) ⊆ (prim 𝔥 \ prim 𝔣) ∪ (prim (z.1.1 * r.1.1) \ prim r.1.1) := by
    intro Q hQ
    have hQc : 0 < cnt Q 𝔠 + cnt Q 𝔫 := by
      rw [mem_prim_iff, cnt_mul K.hc.1 K.hn.1] at hQ; exact hQ
    have hQf : cnt Q 𝔣 = 0 := by
      rcases K.cop_cnt K.hc.1 K.f_ext.1 K.hcf Q with h | h
      · rcases K.cop_cnt K.hn.1 K.f_ext.1 K.hnf Q with h' | h' <;> [omega; exact h']
      · exact h
    have hQd : cnt Q (simplePart r.1.1) = 0 := by
      rcases K.cop_cnt K.hc.1 K.d_ext.1 K.hcd Q with h | h
      · rcases K.cop_cnt K.d_ext.1 K.hn.1 K.hdn Q with h' | h' <;> [exact h'; omega]
      · exact h
    by_cases hQh : Q ∈ prim 𝔥
    · refine Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hQh, ?_⟩)
      rw [mem_prim_iff]; omega
    · refine Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨?_, ?_⟩)
      · rw [mem_prim_iff, cnt_mul z.1.2.1 K.b_ne]
        change 0 < cnt Q (xI 𝔤 𝔞 𝔫 𝔠) + _
        rw [K.cnt_x]; omega
      · rw [(prim_row K.b_ne K.h𝔥).1, Finset.mem_union, not_or]
        exact ⟨hQh, by rw [mem_prim_iff]; omega⟩
  have hone : ∀ Q ∈ (prim 𝔥 \ prim 𝔣) ∪ (prim (z.1.1 * r.1.1) \ prim r.1.1),
      Q ∉ prim (𝔠 * 𝔫) → phiW g (r := r) z 𝔫 𝔠 Q = 1 := by
    intro Q _ hQ
    rw [mem_prim_iff, cnt_mul K.hc.1 K.hn.1] at hQ
    unfold phiW
    have h0 : cnt Q 𝔠 + 3 * cnt Q 𝔫 = 0 := by omega
    rw [h0, mul_zero, pow_zero, one_mul]
    unfold Wv; simp
  have hcomb := Finset.prod_subset hsub hone
  rw [Finset.prod_union hdisj] at hcomb
  unfold Iin
  rw [hcomb]
  simp only [Finset.prod_mul_distrib]
  ring

end L3V

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3I_Char: `χ_P` as a multiplicative character and `x ↦ e(x/π)` as a primitive additive
character of the residue field `L = R / P R`

Standing hypotheses `Good 𝔪 v`: `v` coprime to `𝔪`, `12 ∣ N v − 1`, `v ∤ 𝔇`; and a primitive
sixth root of unity `ω ∈ 𝓞`.

* `chi`: `MulChar L ℂ` with `chi (mk x) = sexticResidueSymbol ι 𝔪 v x`; `chi_neg_one`,
  `chi_pow_six`, `chi_pow_ne_one` (`6 ∤ j`), `chi_cube_eq` (`χ³` is the quadratic character).
* `psi`: `AddChar L ℂ` with `psi (mk x) = e(x / gen P)`; `psi_isPrimitive`.
* `cubicResidueChar_eq`: `ρ_P(x) = χ(x)²` through `𝓞/P ≃ L`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- The standing hypotheses at the prime `v`. -/
structure Good (𝔪 : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) : Prop where
  cop : v.asIdeal ⊔ 𝔪 = ⊤
  twelve : 12 ∣ Ideal.absNorm v.asIdeal - 1
  diff : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal

variable {v : HeightOneSpectrum (𝓞 F)}

lemma Good.notS (h : Good 𝔪 v) : v ∉ placesOf 𝔪 := fun hv =>
  v.isPrime.ne_top (eq_top_iff.2 (h.cop ▸ sup_le le_rfl hv))

lemma Good.ext (h : Good 𝔪 v) : IsExterior 𝔪 v.asIdeal := ⟨v.ne_bot, h.cop⟩

lemma absNorm_ne_one (v : HeightOneSpectrum (𝓞 F)) : Ideal.absNorm v.asIdeal ≠ 1 := by
  rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top

lemma absNorm_pos (v : HeightOneSpectrum (𝓞 F)) : 0 < Ideal.absNorm v.asIdeal := by
  rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot

lemma Good.coprime_six (h : Good 𝔪 v) : (Ideal.absNorm v.asIdeal).Coprime 6 := by
  have h1 := absNorm_pos v
  obtain ⟨k, hk⟩ := h.twelve
  have : Ideal.absNorm v.asIdeal = 12 * k + 1 := by omega
  rw [this, Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, show (12 * k + 1) % 6 = 1 by omega,
    Nat.gcd_one_left]

lemma isMaximal_v (h : Good 𝔪 v) : (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))).IsMaximal :=
  isMaximal_map h.notS

lemma finite_L (h : Good 𝔪 v) : Finite (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  have := finite_quot (𝔪 := 𝔪) h.notS 1
  rwa [pow_one] at this

lemma natCard_L (h : Good 𝔪 v) :
    Nat.card (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) = Ideal.absNorm v.asIdeal := by
  have := natCard_quot (𝔪 := 𝔪) h.notS 1
  rwa [pow_one, pow_one] at this

lemma quotHom_bijective_one (h : v ∉ placesOf 𝔪) :
    Function.Bijective (quotHom 𝔪 v.asIdeal) := by
  have := quotHom_bijective (𝔪 := 𝔪) h 1
  rwa [pow_one] at this

/-! ### The sixth roots of unity -/

section roots

variable (ι : F →+* ℂ)

/-- Choice-free value of a root of unity: if `f ζ = f ω ^ i` then `ι ζ = ι ω ^ i`. -/
lemma iota_eq_pow_of_map {K : Type*} [CommRing K] [IsDomain K] (f : 𝓞 F →+* K) {m : ℕ}
    (hm : 0 < m) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω m) (hωf : IsPrimitiveRoot (f ω) m)
    {ζ : 𝓞 F} (hζ : ζ ^ m = 1) {i : ℕ} (h : f ζ = f ω ^ i) : ι (ζ : F) = ι (ω : F) ^ i := by
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨j, hj, rfl⟩ := hω.eq_pow_of_pow_eq_one hζ
  have hpow : ∀ (z : K) (hz : z ^ m = 1) (n : ℕ), z ^ n = z ^ (n % m) := by
    intro z hz n
    conv_lhs => rw [← Nat.div_add_mod n m, pow_add, pow_mul, hz, one_pow, one_mul]
  have hpowC : ∀ (z : ℂ) (hz : z ^ m = 1) (n : ℕ), z ^ n = z ^ (n % m) := by
    intro z hz n
    conv_lhs => rw [← Nat.div_add_mod n m, pow_add, pow_mul, hz, one_pow, one_mul]
  have h1 : f ω ^ j = f ω ^ (i % m) := by
    rw [← map_pow, h, hpow _ hωf.pow_eq_one]
  have hji : j = i % m := hωf.pow_inj hj (Nat.mod_lt _ hm) h1
  have hιω : ι (ω : F) ^ m = 1 := by
    rw [← map_pow, ← map_pow (algebraMap (𝓞 F) F), hω.pow_eq_one, map_one, map_one]
  rw [show ((ω ^ j : 𝓞 F) : F) = (ω : F) ^ j from map_pow (algebraMap (𝓞 F) F) ω j, map_pow, hji,
    ← hpowC _ hιω]

end roots

section chi

/-- The function underlying `sexticResidueSymbol` on `L = R / P R`. -/
noncomputable def sexFun (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) (y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) : ℂ := by
  classical
  exact if y = 0 then 0 else
    if h : ∃ ζ : 𝓞 F, ζ ^ 6 = 1 ∧
        Ideal.Quotient.mk (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
          (algebraMap (𝓞 F) (SInt 𝔪) ζ) = y ^ ((Ideal.absNorm v.asIdeal - 1) / 6)
    then ι (h.choose : F) else 0

lemma sexticResidueSymbol_eq (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F))
    (x : SInt 𝔪) :
    sexticResidueSymbol ι 𝔪 v.asIdeal x =
      sexFun ι 𝔪 v (Ideal.Quotient.mk (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) x) := by
  unfold sexticResidueSymbol sexFun
  congr 1

variable {ι : F →+* ℂ}

/-- The image of `ω` in `L`. -/
noncomputable abbrev omegaL (ω : 𝓞 F) : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
  Ideal.Quotient.mk _ (algebraMap (𝓞 F) (SInt 𝔪) ω)

lemma omegaL_prim (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) :
    IsPrimitiveRoot (omegaL (𝔪 := 𝔪) (v := v) ω) 6 := by
  have h1 : IsPrimitiveRoot (Ideal.Quotient.mk v.asIdeal ω) 6 :=
    hω.idealQuotient_mk (absNorm_ne_one v) h.coprime_six
  have h2 := h1.map_of_injective (quotHom_bijective_one (𝔪 := 𝔪) h.notS).1
  exact h2

lemma pow_card_sub_one_L (h : Good 𝔪 v)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) :
    y ^ (Ideal.absNorm v.asIdeal - 1) = 1 := by
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  haveI := finite_L h
  letI := Fintype.ofFinite (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  rw [← natCard_L h, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card_sub_one_eq_one y hy

lemma six_mul_e (h : Good 𝔪 v) :
    6 * ((Ideal.absNorm v.asIdeal - 1) / 6) = Ideal.absNorm v.asIdeal - 1 :=
  Nat.mul_div_cancel' ((Nat.dvd_trans (by norm_num) h.twelve))

/-- Every nonzero `y ∈ L` has `y^e` a power of `ω`. -/
lemma exists_pow_e (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) :
    ∃ i : ℕ, i < 6 ∧ y ^ ((Ideal.absNorm v.asIdeal - 1) / 6) = omegaL ω ^ i := by
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have h6 : (y ^ ((Ideal.absNorm v.asIdeal - 1) / 6)) ^ 6 = 1 := by
    rw [← pow_mul, mul_comm, six_mul_e h, pow_card_sub_one_L h hy]
  obtain ⟨i, hi, hi'⟩ := (omegaL_prim h hω).eq_pow_of_pow_eq_one h6
  exact ⟨i, hi, hi'.symm⟩

lemma sexFun_eq_pow (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) {i : ℕ}
    (hi : y ^ ((Ideal.absNorm v.asIdeal - 1) / 6) = omegaL ω ^ i) :
    sexFun ι 𝔪 v y = ι (ω : F) ^ i := by
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have hex : ∃ ζ : 𝓞 F, ζ ^ 6 = 1 ∧
      Ideal.Quotient.mk (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
        (algebraMap (𝓞 F) (SInt 𝔪) ζ) = y ^ ((Ideal.absNorm v.asIdeal - 1) / 6) :=
    ⟨ω ^ i, by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow], by
      rw [map_pow, map_pow, hi]⟩
  classical
  unfold sexFun
  rw [if_neg hy, dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  set f : 𝓞 F →+* SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
    (Ideal.Quotient.mk _).comp (algebraMap (𝓞 F) (SInt 𝔪))
  exact iota_eq_pow_of_map ι f (by norm_num) hω (omegaL_prim h hω) h1 (by
    change Ideal.Quotient.mk _ (algebraMap (𝓞 F) (SInt 𝔪) hex.choose) = omegaL ω ^ i
    rw [h2, hi])

lemma sexFun_zero : sexFun ι 𝔪 v (0 : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) = 0 := by
  classical
  unfold sexFun; rw [if_pos rfl]

lemma iota_omega_prim {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) : IsPrimitiveRoot (ι (ω : F)) 6 :=
  (hω.map_of_injective RingOfIntegers.coe_injective).map_of_injective ι.injective

/-- `χ_P` as a multiplicative character of `L`. -/
noncomputable def chi (ι : F →+* ℂ) (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) :
    MulChar (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ℂ where
  toFun := sexFun ι 𝔪 v
  map_one' := by
    haveI := isMaximal_v h
    letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    rw [sexFun_eq_pow h hω one_ne_zero (i := 0) (by rw [one_pow, pow_zero])]
    simp
  map_mul' := by
    haveI := isMaximal_v h
    letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    intro x y
    by_cases hx : x = 0
    · simp [hx, sexFun_zero]
    by_cases hy : y = 0
    · simp [hy, sexFun_zero]
    obtain ⟨i, -, hi⟩ := exists_pow_e h hω hx
    obtain ⟨j, -, hj⟩ := exists_pow_e h hω hy
    rw [sexFun_eq_pow h hω hx hi, sexFun_eq_pow h hω hy hj,
      sexFun_eq_pow h hω (mul_ne_zero hx hy) (i := i + j) (by rw [mul_pow, hi, hj, pow_add]),
      pow_add]
  map_nonunit' := by
    haveI := isMaximal_v h
    letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    intro a ha
    have : a = 0 := by
      by_contra h'
      exact ha (Ne.isUnit h')
    rw [this]; exact sexFun_zero

lemma chi_apply (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (y) :
    chi ι h hω y = sexFun ι 𝔪 v y := rfl

lemma chi_mk (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (x : SInt 𝔪) :
    chi ι h hω (Ideal.Quotient.mk _ x) = sexticResidueSymbol ι 𝔪 v.asIdeal x :=
  (sexticResidueSymbol_eq ι 𝔪 v x).symm

lemma chi_eq_pow (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) {i : ℕ}
    (hi : y ^ ((Ideal.absNorm v.asIdeal - 1) / 6) = omegaL ω ^ i) :
    chi ι h hω y = ι (ω : F) ^ i :=
  sexFun_eq_pow h hω hy hi

lemma chi_neg_one (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) :
    chi ι h hω (-1) = 1 := by
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have hne : (-1 : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ≠ 0 :=
    neg_ne_zero.2 one_ne_zero
  have heven : Even ((Ideal.absNorm v.asIdeal - 1) / 6) := by
    obtain ⟨k, hk⟩ := h.twelve
    rw [hk, show 12 * k = 6 * (2 * k) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    exact even_two_mul k
  rw [chi_eq_pow h hω hne (i := 0) (by rw [heven.neg_one_pow, pow_zero]), pow_zero]

lemma chi_pow_six_apply (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) :
    chi ι h hω y ^ 6 = 1 := by
  obtain ⟨i, -, hi⟩ := exists_pow_e h hω hy
  rw [chi_eq_pow h hω hy hi, ← pow_mul, mul_comm, pow_mul, (iota_omega_prim hω).pow_eq_one,
    one_pow]

lemma chi_pow_six (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) :
    chi ι h hω ^ 6 = 1 := by
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  ext u
  rw [MulChar.pow_apply' _ (by norm_num), MulChar.one_apply_coe]
  exact chi_pow_six_apply h hω u.ne_zero

/-- `χ` has exact order `6`: `χ^j ≠ 1` unless `6 ∣ j`. -/
lemma chi_pow_ne_one (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) {j : ℕ}
    (hj : ¬ 6 ∣ j) : chi ι h hω ^ j ≠ 1 := by
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  haveI := finite_L h
  letI := Fintype.ofFinite (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  set Q := Ideal.absNorm v.asIdeal
  set e := (Q - 1) / 6
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := (SInt 𝔪 ⧸ v.asIdeal.map
    (algebraMap (𝓞 F) (SInt 𝔪)))ˣ)
  have hog : orderOf γ = Q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, Nat.card_units, natCard_L h]
  obtain ⟨i, hi6, hi⟩ := exists_pow_e h hω
    (y := (γ : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))) γ.ne_zero
  -- `ω^i` is a primitive sixth root
  have hcop : Nat.Coprime i 6 := by
    have hord : orderOf ((γ : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ^ e) = 6 := by
      have hγ' : orderOf (γ : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) = Q - 1 := by
        rw [orderOf_units, hog]
      rw [orderOf_pow' _ (by
        have := six_mul_e h; have hQ := absNorm_ne_one v; have hQ0 := absNorm_pos v
        omega), hγ']
      have := six_mul_e h
      have hQ := absNorm_ne_one v; have hQ0 := absNorm_pos v
      rw [show Q - 1 = 6 * e from (six_mul_e h).symm, Nat.gcd_mul_left_left]
      have he : 0 < e := by omega
      rw [Nat.mul_div_cancel _ he]
    have hprim : IsPrimitiveRoot ((γ : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ^ e) 6 := by
      rw [← hord]; exact IsPrimitiveRoot.orderOf _
    rw [hi] at hprim
    exact ((omegaL_prim h hω).pow_iff_coprime (by norm_num) i).1 hprim
  intro hone
  have h1 : chi ι h hω (γ : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ^ j = 1 := by
    rw [← MulChar.pow_apply' _ (by rintro rfl; exact hj (dvd_zero 6)), hone,
      MulChar.one_apply_coe]
  rw [chi_eq_pow h hω (y := (γ : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))))
    γ.ne_zero hi, ← pow_mul, (iota_omega_prim hω).pow_eq_one_iff_dvd] at h1
  exact hj (hcop.symm.dvd_of_dvd_mul_left h1)

end chi

end C3I

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3I_Gauss: the additive character, Gauss sums and Davenport–Hasse on `L = R / P R`

* `psi g h : AddChar L ℂ`, `psi_mk : psi (mk x) = e(x / gen P)`, `psi_isPrimitive`.
* `card_sqrt`: `#{u | u² = w} = 1 + χ³(w)`; `jacobi_dh`: `χ(4) J(χ, χ) = J(χ³, χ)`.
* Gauss sums `g_j = gaussSum (χ^j) ψ`: `gs_mul_gs_inv`, `gs_three_sq`, `star_gs`, `dh`:
  `χ(4) g₁ g₃ = g₂²`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false


open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

lemma quotLift_mk_sub {I : Ideal (SInt 𝔪)} (x : SInt 𝔪) :
    quotLift (Ideal.Quotient.mk I x) - x ∈ I := by
  rw [← Ideal.Quotient.eq]; exact Function.surjInv_eq Ideal.Quotient.mk_surjective _

lemma mk_quotLift {I : Ideal (SInt 𝔪)} (y : SInt 𝔪 ⧸ I) :
    Ideal.Quotient.mk I (quotLift y) = y :=
  Function.surjInv_eq Ideal.Quotient.mk_surjective _

/-- `e(x / gen 𝔞)` depends only on `x mod 𝔞 R`. -/
lemma sAddChar_div_congr (g : AllowedGen ι 𝔪) (𝔞 : Ideal (𝓞 F)) (h𝔞 : IsExterior 𝔪 𝔞)
    {x x' : SInt 𝔪} (hx : x - x' ∈ 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    sAddChar 𝔪 ((x : F) / (g.gen 𝔞 : F)) = sAddChar 𝔪 ((x' : F) / (g.gen 𝔞 : F)) := by
  have : (x : F) / (g.gen 𝔞 : F) =
      (x' : F) / (g.gen 𝔞 : F) + ((x - x' : SInt 𝔪) : F) / (g.gen 𝔞 : F) := by
    rw [Subalgebra.coe_sub]; ring
  rw [this, C3B.sAddChar_add_mem _ _ (C3B.div_gen_mem g 𝔞 h𝔞 _ hx)]

/-- The additive character `y ↦ e(y / gen P)` of `L`. -/
noncomputable def psi (g : AllowedGen ι 𝔪) (h : Good 𝔪 v) :
    AddChar (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ℂ where
  toFun y := sAddChar 𝔪 ((quotLift y : F) / (g.gen v.asIdeal : F))
  map_zero_eq_one' := by
    have h0 : quotLift (0 : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ∈
        v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, mk_quotLift]
    exact C3B.sAddChar_of_mem _ (C3B.div_gen_mem g _ h.ext _ h0)
  map_add_eq_mul' := by
    intro a b
    have hab : quotLift (a + b) - (quotLift a + quotLift b) ∈
        v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
      rw [← Ideal.Quotient.eq, map_add, mk_quotLift, mk_quotLift, mk_quotLift]
    rw [sAddChar_div_congr g _ h.ext hab, Subalgebra.coe_add, add_div,
      sAddChar_div_gen_add g _ h.ext]

lemma psi_apply (g : AllowedGen ι 𝔪) (h : Good 𝔪 v) (y) :
    psi g h y = sAddChar 𝔪 ((quotLift y : F) / (g.gen v.asIdeal : F)) := rfl

lemma psi_mk (g : AllowedGen ι 𝔪) (h : Good 𝔪 v) (x : SInt 𝔪) :
    psi g h (Ideal.Quotient.mk _ x) = sAddChar 𝔪 ((x : F) / (g.gen v.asIdeal : F)) :=
  sAddChar_div_congr g _ h.ext (quotLift_mk_sub x)

lemma psi_isPrimitive (g : AllowedGen ι 𝔪) (h : Good 𝔪 v) : (psi g h).IsPrimitive := by
  intro a ha hone
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hx : x ∉ (v.asIdeal ^ 1).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [pow_one]; rwa [Ne, Ideal.Quotient.eq_zero_iff_mem] at ha
  obtain ⟨r, hr⟩ := exists_sAddChar_ne_one g h.notS h.cop h.diff le_rfl x hx
  apply hr
  have := congrArg (fun φ => φ (Ideal.Quotient.mk _ r)) hone
  simp only [AddChar.mulShift_apply, AddChar.one_apply] at this
  rw [← map_mul, psi_mk, Subalgebra.coe_mul] at this
  rw [pow_one]
  exact this

/-! ### Characters on the finite field `L` -/

section field

variable (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
variable [Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))]

include h hω

lemma card_L : Fintype.card (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) =
    Ideal.absNorm v.asIdeal := by
  rw [← Nat.card_eq_fintype_card, natCard_L h]

lemma chi_pow_mod (n : ℕ) : chi ι h hω ^ n = chi ι h hω ^ (n % 6) := by
  conv_lhs => rw [← Nat.div_add_mod n 6, pow_add, pow_mul, chi_pow_six h hω, one_pow, one_mul]

lemma chi_pow_neg_one (j : ℕ) : (chi ι h hω ^ j) (-1) = 1 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [pow_zero]
    exact MulChar.one_apply (isUnit_one.neg (α := SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))))
  rw [MulChar.pow_apply' _ hj.ne', chi_neg_one h hω, one_pow]

lemma chi_pow_inv (j k : ℕ) (hjk : (j + k) % 6 = 0) : (chi ι h hω ^ j)⁻¹ = chi ι h hω ^ k := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← pow_add, chi_pow_mod h hω, hjk, pow_zero]

variable (g : AllowedGen ι 𝔪)

/-- `g(φ, ψ⁻¹) = g(φ, ψ)` for the powers of `χ` (as `χ(-1) = 1`). -/
lemma gs_inv_psi (j : ℕ) :
    gaussSum (chi ι h hω ^ j) (psi g h)⁻¹ = gaussSum (chi ι h hω ^ j) (psi g h) := by
  have h1 := chi_pow_neg_one (ι := ι) h hω j
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have := mul_gaussSum_inv_eq_gaussSum (chi ι h hω ^ j) (psi g h)
  rw [h1, one_mul] at this
  exact this

/-- `g_j g_k = N P` for `j + k ≡ 0 (mod 6)`, `6 ∤ j`. -/
lemma gs_mul_gs {j k : ℕ} (hj : ¬ 6 ∣ j) (hjk : (j + k) % 6 = 0) :
    gaussSum (chi ι h hω ^ j) (psi g h) * gaussSum (chi ι h hω ^ k) (psi g h) =
      Ideal.absNorm v.asIdeal := by
  have hχ := chi_pow_ne_one (ι := ι) h hω hj
  have hψ := psi_isPrimitive g h
  have hcard := card_L h hω
  have hinv := chi_pow_inv (ι := ι) h hω j k hjk
  have hk := gs_inv_psi h hω g k
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [hinv, hk, hcard] at this
  exact this

/-- `conj g_j = g_k` for `j + k ≡ 0 (mod 6)`. -/
lemma star_gs (j k : ℕ) (hjk : (j + k) % 6 = 0) :
    starRingEnd ℂ (gaussSum (chi ι h hω ^ j) (psi g h)) = gaussSum (chi ι h hω ^ k) (psi g h) := by
  have hinv := chi_pow_inv (ι := ι) h hω j k hjk
  have hk := gs_inv_psi h hω g k
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have := star_gaussSum_eq (chi ι h hω ^ j) (psi g h)
  rw [hinv, hk] at this
  exact this

end field

end C3I

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3I_HD: the bundle's `γ_j`, `Λ`, `G` through Gauss and Jacobi sums; `Ḡ⁶ = 1` and
`γ₁ γ₂ Λ̄ Ḡ = −1` at a good prime

* `gaussPhase_eq`: `γ_j(P) = (N P)^{-1/2} g(χ^j, ψ)` (`j ≥ 1`);
* `gaussG_eq`: `G(P) = conj(χ(4)) γ₃(P)`;
* `cubicResidueChar_eq`: `ρ_P(x) = χ²(x)` through `𝓞/P ≃ L`; `gaussLambda_eq`:
  `Λ(P) = −(N P)^{-1/2} J(χ², χ²)`;
* `conj_gaussG_pow_six` and `hd_good`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

lemma normalizedFactors_v (v : HeightOneSpectrum (𝓞 F)) :
    normalizedFactors v.asIdeal = {v.asIdeal} := by
  have hirr : Irreducible v.asIdeal := (Ideal.prime_of_isPrime v.ne_bot v.isPrime).irreducible
  rw [normalizedFactors_irreducible hirr, normalize_eq]

lemma residueSymbol_v (x : SInt 𝔪) :
    residueSymbol ι 𝔪 v.asIdeal x = sexticResidueSymbol ι 𝔪 v.asIdeal x := by
  simp [residueSymbol, normalizedFactors_v]

section field

variable (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
  [Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))]
include h hω

lemma chi_mk_quotLift (y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    sexticResidueSymbol ι 𝔪 v.asIdeal (quotLift y) = chi ι h hω y := by
  rw [← chi_mk h hω, mk_quotLift]

/-- `γ_j(P) = (N P)^{-1/2} g(χ^j, ψ)`. -/
lemma gaussPhase_eq (g : AllowedGen ι 𝔪) {j : ℕ} (hj : j ≠ 0) :
    gaussPhase g j v.asIdeal =
      ((Real.sqrt (Ideal.absNorm v.asIdeal) : ℝ) : ℂ)⁻¹ *
        gaussSum (chi ι h hω ^ j) (psi g h) := by
  unfold gaussPhase
  congr 1
  rw [finsum_eq_sum_of_fintype, gaussSum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [residueSymbol_v, chi_mk_quotLift h hω, MulChar.pow_apply' _ hj, psi_apply]

end field

end C3I

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3I_Loc: generators of prime powers and their valuations

* `SixEq 𝔪 x y`: `x = μ⁶ y` for a unit `μ` of `R`; `gen_mul_sixEq`, `gen_top_sixEq`,
  `gen_pow_add`, `gen_pow_mul`.
* `val_gen`: `v(gen(P^j)) = exp(-j)`; `val_unit`; `mul_mem_iff`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

/-- `x = μ⁶ y` for a unit `μ` of `R`. -/
def SixEq (𝔪 : Ideal (𝓞 F)) (x y : SInt 𝔪) : Prop := ∃ μ : (SInt 𝔪)ˣ, x = (μ : SInt 𝔪) ^ 6 * y

lemma SixEq.refl (x : SInt 𝔪) : SixEq 𝔪 x x := ⟨1, by simp⟩

lemma SixEq.trans {x y z : SInt 𝔪} (h1 : SixEq 𝔪 x y) (h2 : SixEq 𝔪 y z) : SixEq 𝔪 x z := by
  obtain ⟨μ, rfl⟩ := h1
  obtain ⟨ν, rfl⟩ := h2
  exact ⟨μ * ν, by rw [Units.val_mul, mul_pow]; ring⟩

lemma SixEq.mul {x y x' y' : SInt 𝔪} (h1 : SixEq 𝔪 x y) (h2 : SixEq 𝔪 x' y') :
    SixEq 𝔪 (x * x') (y * y') := by
  obtain ⟨μ, rfl⟩ := h1
  obtain ⟨ν, rfl⟩ := h2
  exact ⟨μ * ν, by rw [Units.val_mul, mul_pow]; ring⟩

/-- `gen(IJ) = μ⁶ gen(I) gen(J)`. -/
lemma gen_mul_sixEq (g : AllowedGen ι 𝔪) {I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I)
    (hJ : IsExterior 𝔪 J) : SixEq 𝔪 (g.gen (I * J)) (g.gen I * g.gen J) := by
  obtain ⟨ε, hε⟩ := g.gen_mul I J hI hJ
  refine ⟨Set.unitEquivUnitsInteger (placesOf 𝔪) F ε, Subtype.ext ?_⟩
  rw [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_mul, hε, mul_assoc]
  rfl

lemma isExterior_top' : IsExterior 𝔪 (⊤ : Ideal (𝓞 F)) := ⟨top_ne_bot, top_sup_eq _⟩

/-- `gen ⊤` is a sixth power of a unit. -/
lemma gen_top_sixEq (g : AllowedGen ι 𝔪) : SixEq 𝔪 (g.gen ⊤) 1 := by
  obtain ⟨μ, hμ⟩ := C3B.isUnit_gen_top g
  have h := gen_mul_sixEq g (isExterior_top' (𝔪 := 𝔪)) isExterior_top'
  rw [Ideal.top_mul] at h
  obtain ⟨ν, hν⟩ := h
  refine ⟨ν⁻¹, ?_⟩
  rw [mul_one, ← hμ]
  rw [← hμ] at hν
  have h2 : (ν : SInt 𝔪) ^ 6 * μ = 1 := by
    apply mul_left_cancel₀ μ.ne_zero
    linear_combination (-1 : SInt 𝔪) * hν
  calc (μ : SInt 𝔪) = ((ν⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) ^ 6 * ((ν : SInt 𝔪) ^ 6 * μ) := by
        rw [← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
    _ = _ := by rw [h2, mul_one]

section prime

variable (g : AllowedGen ι 𝔪) (h : Good 𝔪 v)
include h

lemma ext_pow (j : ℕ) : IsExterior 𝔪 (v.asIdeal ^ j) := isExterior_pow h.ext j

/-! ### Valuations -/

lemma val_unit (μ : (SInt 𝔪)ˣ) : v.valuation F ((μ : SInt 𝔪) : F) = 1 := by
  have h1 := val_le_one h.notS (μ : SInt 𝔪)
  have h2 := val_le_one h.notS ((μ⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪)
  have h3 : v.valuation F ((μ : SInt 𝔪) : F) * v.valuation F (((μ⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = 1 := by
    rw [← map_mul, ← Subalgebra.coe_mul, Units.mul_inv]; simp
  exact eq_one_of_one_le_mul_left h1 h2 h3.ge

lemma gen_mem (j : ℕ) :
    g.gen (v.asIdeal ^ j) ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  rw [← g.span_gen _ (ext_pow h j)]; exact Ideal.mem_span_singleton_self _

lemma val_pi : v.valuation F (g.gen v.asIdeal : F) = exp (-1 : ℤ) := by
  have hmem := gen_mem g h 1
  rw [pow_one] at hmem
  apply le_antisymm
  · have := val_le_of_mem h.notS 1 (by rw [pow_one]; exact hmem)
    simpa using this
  · obtain ⟨p, hp⟩ := exists_uniformizer (v := v)
    have hpm : algebraMap (𝓞 F) (SInt 𝔪) p ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
      apply Ideal.mem_map_of_mem
      rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F), hp]
      exact exp_lt_exp.2 (by norm_num) |>.trans_eq exp_zero
    rw [← g.span_gen _ h.ext, Ideal.mem_span_singleton'] at hpm
    obtain ⟨r, hr⟩ := hpm
    have := congrArg (fun z : SInt 𝔪 => v.valuation F (z : F)) hr
    simp only [Subalgebra.coe_mul, map_mul, coe_alg, hp] at this
    rw [← this]
    calc v.valuation F (r : F) * v.valuation F (g.gen v.asIdeal : F)
        ≤ 1 * v.valuation F (g.gen v.asIdeal : F) := mul_le_mul_left (val_le_one h.notS r) _
      _ = _ := one_mul _

lemma val_eq_one_of_not_mem {q : SInt 𝔪} (hq : q ∉ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    v.valuation F (q : F) = 1 := by
  apply le_antisymm (val_le_one h.notS q)
  have := exp_le_val_of_not_mem h.notS 0 q (by rwa [zero_add, pow_one])
  simpa using this

end prime

end C3I

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3V_Alg1: `ν = μ⁶ ε_u a′ c′ n′³ / (d f)²` (6.21) and the multiplicative splittings

* `nu_decomp`: the key's frequency is `μ⁶ · ε_u a′ c′ n′³ (d²)^{−1} (f²)^{−1}` with `μ ∈ U_S`;
* `uSym_nu`, `L_nu`, `cls_nu`: the unit-part symbol, the `S`-character and the class of `ν` split
  accordingly (`uSym(μ⁶) = 1`, `L(U_S) = 1`, `cls(U_S⁶) = 1`);
* `arg_eq`: the sheet norm `|ν|_S / l = N𝔞′ N𝔠′ N𝔫′³ / (N𝔡² N𝔣² l)`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

lemma gen_pow_sixEq' (g : AllowedGen ι 𝔪) {I : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (n : ℕ) :
    C3I.SixEq 𝔪 (g.gen (I ^ n)) (g.gen I ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, Ideal.one_eq_top]; exact C3I.gen_top_sixEq g
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (C3I.gen_mul_sixEq g (C3I.isExterior_pow hI n) hI).trans (ih.mul (C3I.SixEq.refl _))

/-- The `S`-unit attached to a unit of `R`. -/
noncomputable def toSU (μ : (SInt 𝔪)ˣ) : SUnit 𝔪 := (Set.unitEquivUnitsInteger (placesOf 𝔪) F).symm μ

lemma toSU_coe (μ : (SInt 𝔪)ˣ) : (((toSU μ : SUnit 𝔪) : Fˣ) : F) = ((μ : SInt 𝔪) : F) := rfl

lemma rep_eq_toSU (u : SClass 𝔪) : ∃ μ : (SInt 𝔪)ˣ, ((u.rep : SInt 𝔪) : F) = ((μ : SInt 𝔪) : F) :=
  ⟨_, rfl⟩

lemma unit_coe_ne (μ : (SInt 𝔪)ˣ) : ((μ : SInt 𝔪) : F) ≠ 0 := by
  intro h0
  have : (μ : SInt 𝔪) = 0 := Subtype.ext h0
  exact μ.ne_zero this

variable (g : AllowedGen ι 𝔪) {r : RowClass 𝔪} {𝔥 𝔣 𝔤 𝔞 𝔫 𝔠 : Ideal (𝓞 F)}
  (K : KeyHyp r 𝔥 𝔣 𝔤 𝔞 𝔫 𝔠) (u : SClass 𝔪)
include K

/-- (6.21) `ν = μ⁶ · ε_u a′ c′ n′³ (d²)^{−1} (f²)^{−1}`. -/
lemma nu_decomp : ∃ μ : (SInt 𝔪)ˣ, nu g r (zK K u) = ((μ : SInt 𝔪) : F) ^ 6 *
    ((u.rep : SInt 𝔪) : F) * gF g 𝔞 * gF g 𝔠 * gF g 𝔫 ^ 3 * ((gF g (simplePart r.1.1)) ^ 2)⁻¹ *
      ((gF g 𝔣) ^ 2)⁻¹ := by
  have hx : C3I.SixEq 𝔪 (g.gen (xI 𝔤 𝔞 𝔫 𝔠))
      (g.gen 𝔤 ^ 2 * g.gen 𝔞 * g.gen 𝔠 * g.gen 𝔫 ^ 3) := by
    unfold xI
    have e1 := C3I.gen_mul_sixEq g (C3I.isExterior_mul (C3I.isExterior_mul
      (C3I.isExterior_pow K.g_ext 2) K.ha) K.hc) (C3I.isExterior_pow K.hn 3)
    have e2 := C3I.gen_mul_sixEq g (C3I.isExterior_mul (C3I.isExterior_pow K.g_ext 2) K.ha) K.hc
    have e3 := C3I.gen_mul_sixEq g (C3I.isExterior_pow K.g_ext 2) K.ha
    exact e1.trans (((e2.trans ((e3.trans ((gen_pow_sixEq' g K.g_ext 2).mul
      (C3I.SixEq.refl _))).mul (C3I.SixEq.refl _))).mul (gen_pow_sixEq' g K.hn 3)))
  have hb : C3I.SixEq 𝔪 (g.gen r.1.1) (g.gen 𝔣 * g.gen 𝔤 * g.gen (simplePart r.1.1)) := by
    have hr : r.1.1 = 𝔣 * 𝔤 * simplePart r.1.1 := by rw [← K.hfg, K.h𝔥]
    have e := (C3I.gen_mul_sixEq g (C3I.isExterior_mul K.f_ext K.g_ext) K.d_ext).trans
      ((C3I.gen_mul_sixEq g K.f_ext K.g_ext).mul (C3I.SixEq.refl (g.gen (simplePart r.1.1))))
    rw [← hr] at e
    exact e
  obtain ⟨μ1, h1⟩ := hx
  obtain ⟨μ2, h2⟩ := hb
  refine ⟨μ1 * μ2⁻¹ * μ2⁻¹, ?_⟩
  have hG := C3B.gen_ne_zero g 𝔤 K.g_ext
  have hf := C3B.gen_ne_zero g 𝔣 K.f_ext
  have hd := C3B.gen_ne_zero g _ K.d_ext
  have hm2 := unit_coe_ne μ2
  have hinv : ((↑(μ2⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = (((μ2 : SInt 𝔪) : F))⁻¹ := by
    have : ((μ2 : SInt 𝔪) : F) * ((↑(μ2⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = 1 := by
      rw [← Subalgebra.coe_mul, Units.mul_inv]; rfl
    exact eq_inv_of_mul_eq_one_right this
  unfold nu rowElt
  change ((u.rep * g.gen (xI 𝔤 𝔞 𝔫 𝔠) : SInt 𝔪) : F) / ((g.gen r.1.1 : SInt 𝔪) : F) ^ 2 = _
  rw [h1, h2]
  simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, Units.val_mul, hinv]
  unfold gF
  field_simp

end L3V

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3V_Alg2: splitting `uSym(ν)`, `L(ν)`, `[ν]` and the sheet norm along (6.21) -/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

section Lcls

variable {g : AllowedGen ι 𝔪} {χ : HeckeChar F 𝔪} (D : Data χ g)

lemma L_one (υ : SClass 𝔪) : D.L υ 1 = 1 := by
  have h := D.hL υ 1 1 one_ne_zero one_ne_zero
  have hn := D.hLn υ 1 one_ne_zero
  rw [mul_one] at h
  have h0 : D.L υ 1 ≠ 0 := by intro h0; rw [h0, norm_zero] at hn; exact zero_ne_one hn
  exact (mul_left_cancel₀ h0 (h.symm.trans (mul_one _).symm))

lemma L_inv (υ : SClass 𝔪) {a : F} (ha : a ≠ 0) : D.L υ a⁻¹ = (D.L υ a)⁻¹ := by
  have h := D.hL υ a a⁻¹ ha (inv_ne_zero ha)
  rw [mul_inv_cancel₀ ha, L_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

lemma L_pow (υ : SClass 𝔪) {a : F} (ha : a ≠ 0) (n : ℕ) : D.L υ (a ^ n) = D.L υ a ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, L_one]
  | succ n ih => rw [pow_succ, D.hL υ _ _ (pow_ne_zero _ ha) ha, ih, pow_succ]

lemma L_unit (υ : SClass 𝔪) (μ : (SInt 𝔪)ˣ) : D.L υ ((μ : SInt 𝔪) : F) = 1 := by
  rw [← toSU_coe μ]; exact D.hLu υ _

lemma cls_one : D.cls 1 = 1 := by
  have h := D.hcls 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  exact (mul_left_cancel (h.symm.trans (mul_one _).symm))

lemma cls_inv {a : F} (ha : a ≠ 0) : D.cls a⁻¹ = (D.cls a)⁻¹ := by
  have h := D.hcls a a⁻¹ ha (inv_ne_zero ha)
  rw [mul_inv_cancel₀ ha, cls_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

lemma cls_pow {a : F} (ha : a ≠ 0) (n : ℕ) : D.cls (a ^ n) = D.cls a ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, cls_one]
  | succ n ih => rw [pow_succ, D.hcls _ _ (pow_ne_zero _ ha) ha, ih, pow_succ]

lemma cls_unit6 (μ : (SInt 𝔪)ˣ) : D.cls (((μ : SInt 𝔪) : F) ^ 6) = 1 := by
  rw [← toSU_coe μ]; exact D.hcls6 _

end Lcls

variable (E : Env ι 𝔪) (g : AllowedGen ι 𝔪) {χ : HeckeChar F 𝔪} (D : Data χ g)
  {r : RowClass 𝔪} {𝔥 𝔣 𝔤 𝔞 𝔫 𝔠 : Ideal (𝓞 F)} (K : KeyHyp r 𝔥 𝔣 𝔤 𝔞 𝔫 𝔠) (u : SClass 𝔪)

/-- Nonvanishing of the pieces of `ν`. -/
structure NZ (a b c d e f : F) : Prop where
  a : a ≠ 0
  b : b ≠ 0
  c : c ≠ 0
  d : d ≠ 0
  e : e ≠ 0
  f : f ≠ 0

include K in
lemma nz : NZ ((u.rep : SInt 𝔪) : F) (gF g 𝔞) (gF g 𝔠) (gF g 𝔫) (gF g (simplePart r.1.1))
    (gF g 𝔣) :=
  ⟨rep_ne_zero u, C3B.gen_ne_zero g _ K.ha, C3B.gen_ne_zero g _ K.hc, C3B.gen_ne_zero g _ K.hn,
    C3B.gen_ne_zero g _ K.d_ext, C3B.gen_ne_zero g _ K.f_ext⟩

include E K in
lemma uSym_nu {P : Ideal (𝓞 F)} (hP : P.IsPrime) (he : IsExterior 𝔪 P) :
    uSym g P (nu g r (zK K u)) = uSym g P ((u.rep : SInt 𝔪) : F) * uSym g P (gF g 𝔞) *
      uSym g P (gF g 𝔠) * uSym g P (gF g 𝔫) ^ 3 * ((uSym g P (gF g (simplePart r.1.1)))⁻¹) ^ 2 *
      ((uSym g P (gF g 𝔣))⁻¹) ^ 2 := by
  obtain ⟨μ, hμ⟩ := nu_decomp g K u
  have N := nz g K u
  have hμ0 := unit_coe_ne μ
  rw [hμ]
  have m := fun {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) => uSym_mulE E g hP he hx hy
  have p1 := mul_ne_zero (pow_ne_zero 6 hμ0) N.a
  have p2 := mul_ne_zero p1 N.b
  have p3 := mul_ne_zero p2 N.c
  have p4 := mul_ne_zero p3 (pow_ne_zero 3 N.d)
  have he2 := inv_ne_zero (pow_ne_zero 2 N.e)
  have hf2 := inv_ne_zero (pow_ne_zero 2 N.f)
  have p5 := mul_ne_zero p4 he2
  rw [m p5 hf2, m p4 he2, m p3 (pow_ne_zero 3 N.d), m p2 N.c, m p1 N.b,
    m (pow_ne_zero _ hμ0) N.a, uSym_pow_six_unitE E g hP he μ, one_mul,
    uSym_powE E g hP he N.d, uSym_invE E g hP he (pow_ne_zero _ N.e),
    uSym_invE E g hP he (pow_ne_zero _ N.f), uSym_powE E g hP he N.e, uSym_powE E g hP he N.f,
    inv_pow, inv_pow]

include K in
lemma L_nu (υ : SClass 𝔪) :
    (D.L υ (nu g r (zK K u)))⁻¹ = (D.L υ (gF g 𝔞))⁻¹ * (D.L υ (gF g 𝔠))⁻¹ *
      ((D.L υ (gF g 𝔫))⁻¹) ^ 3 * D.L υ (gF g (simplePart r.1.1)) ^ 2 * D.L υ (gF g 𝔣) ^ 2 := by
  obtain ⟨μ, hμ⟩ := nu_decomp g K u
  have N := nz g K u
  have hμ0 := unit_coe_ne μ
  have hr : ∃ μ' : (SInt 𝔪)ˣ, ((u.rep : SInt 𝔪) : F) = ((μ' : SInt 𝔪) : F) := rep_eq_toSU u
  obtain ⟨μ', hμ'⟩ := hr
  rw [hμ]
  have m := D.hL υ
  have p1 := mul_ne_zero (pow_ne_zero 6 hμ0) N.a
  have p2 := mul_ne_zero p1 N.b
  have p3 := mul_ne_zero p2 N.c
  have p4 := mul_ne_zero p3 (pow_ne_zero 3 N.d)
  have he2 := inv_ne_zero (pow_ne_zero 2 N.e)
  have hf2 := inv_ne_zero (pow_ne_zero 2 N.f)
  have p5 := mul_ne_zero p4 he2
  rw [m _ _ p5 hf2, m _ _ p4 he2, m _ _ p3 (pow_ne_zero 3 N.d), m _ _ p2 N.c, m _ _ p1 N.b,
    m _ _ (pow_ne_zero _ hμ0) N.a, hμ', L_unit D υ μ', L_pow D υ hμ0, L_unit D υ μ, one_pow,
    L_inv D υ (pow_ne_zero _ N.e), L_inv D υ (pow_ne_zero _ N.f), L_pow D υ N.d, L_pow D υ N.e,
    L_pow D υ N.f]
  have h1 := D.hLn υ _ N.b; have h2 := D.hLn υ _ N.c; have h3 := D.hLn υ _ N.d
  have h4 := D.hLn υ _ N.e; have h5 := D.hLn υ _ N.f
  have ne : ∀ {z : ℂ}, ‖z‖ = 1 → z ≠ 0 := fun hz h0 => by rw [h0, norm_zero] at hz; exact zero_ne_one hz
  field_simp [ne h1, ne h2, ne h3, ne h4, ne h5]

include K in
lemma cls_nu :
    D.cls (nu g r (zK K u)) = D.cls ((u.rep : SInt 𝔪) : F) * D.cls (gF g 𝔞) * D.cls (gF g 𝔠) *
      D.cls (gF g 𝔫) ^ 3 * (D.cls (gF g (simplePart r.1.1)) ^ 2)⁻¹ * (D.cls (gF g 𝔣) ^ 2)⁻¹ := by
  obtain ⟨μ, hμ⟩ := nu_decomp g K u
  have N := nz g K u
  have hμ0 := unit_coe_ne μ
  rw [hμ]
  have m := D.hcls
  have p1 := mul_ne_zero (pow_ne_zero 6 hμ0) N.a
  have p2 := mul_ne_zero p1 N.b
  have p3 := mul_ne_zero p2 N.c
  have p4 := mul_ne_zero p3 (pow_ne_zero 3 N.d)
  have he2 := inv_ne_zero (pow_ne_zero 2 N.e)
  have hf2 := inv_ne_zero (pow_ne_zero 2 N.f)
  have p5 := mul_ne_zero p4 he2
  rw [m _ _ p5 hf2, m _ _ p4 he2, m _ _ p3 (pow_ne_zero 3 N.d), m _ _ p2 N.c, m _ _ p1 N.b,
    m _ _ (pow_ne_zero _ hμ0) N.a, cls_unit6 D μ, one_mul, cls_pow D N.d,
    cls_inv D (pow_ne_zero _ N.e), cls_inv D (pow_ne_zero _ N.f), cls_pow D N.e, cls_pow D N.f]

lemma absNorm_pos_real {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : (0 : ℝ) < Ideal.absNorm I :=
  Nat.cast_pos.2 (Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]))

include K in
lemma arg_eq (l : ℝ) (hl : 0 < l) :
    (Ideal.absNorm (zK K u).1.1 : ℝ) / ((Ideal.absNorm r.1.1 : ℝ) ^ 2 * l) =
      l⁻¹ * Ideal.absNorm 𝔞 * Ideal.absNorm 𝔠 * (Ideal.absNorm 𝔫 : ℝ) ^ 3 /
        ((Ideal.absNorm (simplePart r.1.1) : ℝ) ^ 2 * (Ideal.absNorm 𝔣 : ℝ) ^ 2) := by
  have hr : r.1.1 = 𝔣 * 𝔤 * simplePart r.1.1 := by rw [← K.hfg, K.h𝔥]
  change (Ideal.absNorm (xI 𝔤 𝔞 𝔫 𝔠) : ℝ) / _ = _
  conv_lhs => rw [hr]
  unfold xI
  simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]
  have hg : (Ideal.absNorm 𝔤 : ℝ) ≠ 0 := by
    have := absNorm_pos_real K.g_ext.1; linarith
  have hf : (Ideal.absNorm 𝔣 : ℝ) ≠ 0 := by
    have := absNorm_pos_real K.f_ext.1; linarith
  have hd : (Ideal.absNorm (simplePart r.1.1) : ℝ) ≠ 0 := by
    have := absNorm_pos_real K.d_ext.1; linarith
  have hl' := hl.ne'
  field_simp

end L3V

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3V_Alg3: the spherical magnitudes and the quadratic pairing (6.28)

* `phi_prod`: `∏_{𝔮 ∣ 𝔠′𝔫′} U_𝔮^{2y} W_y = N𝔫′^{−1} N𝔠′^{−1/2} ∏_{𝔮 ∣ 𝔠′} γ₂(𝔮) U_𝔮²`;
* `pairing` (6.28): `∏_{𝔭∣𝔡} χ_𝔭(c′)^{13} · ∏_{𝔮∣𝔠′} χ_𝔮(d)^{−4} = χ_𝔡(c′)³`, by reciprocity
  (`1 − 4 ≡ 3 mod 6`, here `13 − 4 = 9 ≡ 3`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

lemma Wv_c3n (g : AllowedGen ι 𝔪) (Q : Ideal (𝓞 F)) (hq : (0 : ℝ) < Ideal.absNorm Q) (c n : ℕ)
    (hc : c ≤ 1) :
    Wv g Q (c + 3 * n) = ((((Ideal.absNorm Q : ℝ) ^ n)⁻¹ : ℝ) : ℂ) *
      (if c = 1 then (((Real.sqrt (Ideal.absNorm Q))⁻¹ : ℝ) : ℂ) * gaussPhase g 2 Q else 1) := by
  unfold Wv
  rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl
  · rw [if_pos (by omega), if_neg (by norm_num), mul_one,
      show (0 + 3 * n) / 3 = n by omega, Real.rpow_neg hq.le, Real.rpow_natCast]
  · rw [if_neg (by omega), if_pos (by omega), if_pos rfl, show (1 + 3 * n) / 3 = n by omega,
      Real.rpow_sub hq, Real.rpow_neg hq.le, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
    push_cast; ring

variable (E : Env ι 𝔪) (g : AllowedGen ι 𝔪) {r : RowClass 𝔪} {𝔥 𝔣 𝔤 𝔞 𝔫 𝔠 : Ideal (𝓞 F)}
  (K : KeyHyp r 𝔥 𝔣 𝔤 𝔞 𝔫 𝔠) (u : SClass 𝔪)

include E K in
lemma phiW_eq {Q : Ideal (𝓞 F)} (hQ : Q ∈ prim (𝔠 * 𝔫)) :
    phiW g (r := r) (zK K u) 𝔫 𝔠 Q =
      ((((Ideal.absNorm Q : ℝ) ^ cnt Q 𝔫)⁻¹ : ℝ) : ℂ) *
        (if cnt Q 𝔠 = 1 then (((Real.sqrt (Ideal.absNorm Q))⁻¹ : ℝ) : ℂ) * gaussPhase g 2 Q *
          uSym g Q (nu g r (zK K u)) ^ 2 else 1) := by
  have hcn : IsExterior 𝔪 (𝔠 * 𝔫) := C3I.isExterior_mul K.hc K.hn
  obtain ⟨hQp, hQe⟩ := (⟨(prime_of_mem_prim hQ).1, exterior_of_prim hcn hQ⟩ :
    Q.IsPrime ∧ IsExterior 𝔪 Q)
  have hU6 : uSym g Q (nu g r (zK K u)) ^ 6 = 1 := uSym_pow_sixE E g hQp hQe (nu_ne_zero g r _)
  have hq : (0 : ℝ) < Ideal.absNorm Q := absNorm_pos_real hQe.1
  unfold phiW
  rw [Wv_c3n g Q hq _ _ (K.cnt_c_le Q)]
  have hpow : uSym g Q (nu g r (zK K u)) ^ (2 * (cnt Q 𝔠 + 3 * cnt Q 𝔫)) =
      uSym g Q (nu g r (zK K u)) ^ (2 * cnt Q 𝔠) := by
    rw [show 2 * (cnt Q 𝔠 + 3 * cnt Q 𝔫) = 2 * cnt Q 𝔠 + 6 * cnt Q 𝔫 by ring, pow_add,
      pow_mul (uSym g Q (nu g r (zK K u))) 6 (cnt Q 𝔫), hU6, one_pow, mul_one]
  rw [hpow]
  rcases (by have := K.cnt_c_le Q; omega : cnt Q 𝔠 = 0 ∨ cnt Q 𝔠 = 1) with h0 | h1
  · rw [h0, if_neg (by norm_num), if_neg (by norm_num)]; ring
  · rw [h1, if_pos rfl, if_pos rfl]; ring

include E K in
lemma phi_prod :
    ∏ Q ∈ prim (𝔠 * 𝔫), phiW g (r := r) (zK K u) 𝔫 𝔠 Q =
      ((Ideal.absNorm 𝔫 : ℂ))⁻¹ * (((Real.sqrt (Ideal.absNorm 𝔠)) : ℝ) : ℂ)⁻¹ *
        ∏ Q ∈ prim 𝔠, gaussPhase g 2 Q * uSym g Q (nu g r (zK K u)) ^ 2 := by
  classical
  rw [Finset.prod_congr rfl fun Q hQ => phiW_eq E g K u hQ, Finset.prod_mul_distrib]
  have hcn0 : 𝔠 * 𝔫 ≠ ⊥ := mul_ne_zero K.hc.1 K.hn.1
  have hsubn : prim 𝔫 ⊆ prim (𝔠 * 𝔫) := by rw [prim_mul K.hc.1 K.hn.1]; exact Finset.subset_union_right
  have hsubc : prim 𝔠 ⊆ prim (𝔠 * 𝔫) := by rw [prim_mul K.hc.1 K.hn.1]; exact Finset.subset_union_left
  -- the `𝔫`-magnitudes
  have h1 : ∏ Q ∈ prim (𝔠 * 𝔫), ((((Ideal.absNorm Q : ℝ) ^ cnt Q 𝔫)⁻¹ : ℝ) : ℂ) =
      ((Ideal.absNorm 𝔫 : ℂ))⁻¹ := by
    rw [← Complex.ofReal_prod, Finset.prod_inv_distrib,
      ← Finset.prod_subset hsubn (fun Q _ hQ => by
        rw [mem_prim_iff] at hQ; rw [show cnt Q 𝔫 = 0 by omega, pow_zero]),
      ← absNorm_eq_prod 𝔫 K.hn.1]
    push_cast; rfl
  -- the `𝔠`-part
  have h2 : ∏ Q ∈ prim (𝔠 * 𝔫), (if cnt Q 𝔠 = 1 then (((Real.sqrt (Ideal.absNorm Q))⁻¹ : ℝ) : ℂ) *
        gaussPhase g 2 Q * uSym g Q (nu g r (zK K u)) ^ 2 else 1) =
      ∏ Q ∈ prim 𝔠, (((Real.sqrt (Ideal.absNorm Q))⁻¹ : ℝ) : ℂ) *
        gaussPhase g 2 Q * uSym g Q (nu g r (zK K u)) ^ 2 := by
    rw [← Finset.prod_filter]
    congr 1
    ext Q
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨-, h⟩; rw [mem_prim_iff]; omega
    · intro h
      refine ⟨hsubc h, ?_⟩
      have := mem_prim_iff.1 h; have := K.cnt_c_le Q; omega
  have h3 : ∏ Q ∈ prim 𝔠, (((Real.sqrt (Ideal.absNorm Q))⁻¹ : ℝ) : ℂ) =
      (((Real.sqrt (Ideal.absNorm 𝔠)) : ℝ) : ℂ)⁻¹ := by
    rw [← Complex.ofReal_prod, Finset.prod_inv_distrib, ← Real.sqrt_prod _ (fun _ _ => Nat.cast_nonneg _)]
    have hc : (Ideal.absNorm 𝔠 : ℝ) = ∏ Q ∈ prim 𝔠, (Ideal.absNorm Q : ℝ) := by
      rw [absNorm_eq_prod 𝔠 K.hc.1]
      refine Finset.prod_congr rfl fun Q hQ => ?_
      have := mem_prim_iff.1 hQ; have := K.cnt_c_le Q
      rw [show cnt Q 𝔠 = 1 by omega, pow_one]
    rw [hc]; push_cast; rfl
  rw [h1, h2, Finset.prod_congr rfl (fun Q _ => mul_assoc _ _ _), Finset.prod_mul_distrib, h3]
  ring

include E K in
/-- (6.28): the row–column pairing. -/
lemma pairing :
    (∏ P ∈ prim (simplePart r.1.1), uSym g P (gF g 𝔠) ^ 13) *
      (∏ Q ∈ prim 𝔠, ((uSym g Q (gF g (simplePart r.1.1)))⁻¹) ^ 4) =
      residueSymbol ι 𝔪 (simplePart r.1.1) (g.gen 𝔠) ^ 3 := by
  set 𝔡 := simplePart r.1.1
  have hdsq : Squarefree 𝔡 := L2D_simplePart_squarefree _ K.b_ne
  -- `uSym` at a prime not dividing the generator's ideal is the residue symbol
  have hu : ∀ {I J : Ideal (𝓞 F)}, IsExterior 𝔪 I → IsExterior 𝔪 J → I ⊔ J = ⊤ → ∀ P ∈ prim I,
      uSym g P (gF g J) = sexticResidueSymbol ι 𝔪 P (g.gen J) := by
    intro I J hI hJ hIJ P hP
    obtain ⟨hPp, hPe⟩ := (⟨(prime_of_mem_prim hP).1, exterior_of_prim hI hP⟩ :
      P.IsPrime ∧ IsExterior 𝔪 P)
    have hJP : cnt P J = 0 := by
      rcases (sup_eq_top_iff_cnt hI.1 hJ.1).1 hIJ P with h | h
      · have := mem_prim_iff.1 hP; omega
      · exact h
    have hnm : g.gen J ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
      rw [(E.loc g P hPp hPe).mem_iff, (E.loc g P hPp hPe).val_gen J hJ]
      change WithZero.exp (-((cnt P J : ℕ) : ℤ)) = _
      rw [hJP]; simp
    exact uSym_SIntE E g hPp hPe hnm
  have hX : ∏ P ∈ prim 𝔡, uSym g P (gF g 𝔠) = residueSymbol ι 𝔪 𝔡 (g.gen 𝔠) := by
    rw [residueSymbol_sqfree ι 𝔪 𝔡 K.d_ext.1 hdsq]
    exact Finset.prod_congr rfl (hu K.d_ext K.hc (by rw [sup_comm]; exact K.hcd))
  have hY : ∏ Q ∈ prim 𝔠, uSym g Q (gF g 𝔡) = residueSymbol ι 𝔪 𝔡 (g.gen 𝔠) := by
    rw [← residueSymbol_recip (E.hχ g) g K.d_ext 𝔠 K.hc K.hcd,
      residueSymbol_sqfree ι 𝔪 𝔠 K.hc.1 K.hcs]
    exact Finset.prod_congr rfl (hu K.hc K.d_ext K.hcd)
  have h6 : ∀ P ∈ prim 𝔡, uSym g P (gF g 𝔠) ^ 6 = 1 := by
    intro P hP
    obtain ⟨hPp, hPe⟩ := (⟨(prime_of_mem_prim hP).1, exterior_of_prim K.d_ext hP⟩ :
      P.IsPrime ∧ IsExterior 𝔪 P)
    exact uSym_pow_sixE E g hPp hPe (C3B.gen_ne_zero g _ K.hc)
  have hX6 : residueSymbol ι 𝔪 𝔡 (g.gen 𝔠) ^ 6 = 1 := by
    rw [← hX, ← Finset.prod_pow]; exact Finset.prod_eq_one h6
  have hX0 : residueSymbol ι 𝔪 𝔡 (g.gen 𝔠) ≠ 0 := by
    intro h0; rw [h0] at hX6; norm_num at hX6
  rw [Finset.prod_pow, Finset.prod_pow, Finset.prod_inv_distrib, hX, hY]
  have : residueSymbol ι 𝔪 𝔡 (g.gen 𝔠) ^ 13 = residueSymbol ι 𝔪 𝔡 (g.gen 𝔠) ^ 7 := by
    rw [show 13 = 6 + 7 by norm_num, pow_add, hX6, one_mul]
  rw [this]
  field_simp

end L3V

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3V_KeyId: the factor separation (6.29) at a key

`key_identity`: for a key with matching class slices, the cut's summand at the key's frequency,
`E_{prim 𝔣}(ν) L_υ(ν)^{−1} H_{υ,[ν]}(|ν|_S/l)`, equals Cut63V's summand
`ω/q_𝔫′ · ρ(𝔡) · λ(𝔠′) χ_𝔡(c′)³ q_𝔠′^{−1/2} H(...)`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

variable (E : Env ι 𝔪) (g : AllowedGen ι 𝔪) {χ : HeckeChar F 𝔪} (D : Data χ g) {N : ℕ}
  (eU : Fin N ≃ SClass 𝔪) {r : RowClass 𝔪} {𝔥 𝔣 𝔤 𝔞 𝔫 𝔠 : Ideal (𝓞 F)}
  (K : KeyHyp r 𝔥 𝔣 𝔤 𝔞 𝔫 𝔠)

include E K

theorem key_identity (s : TT D N) (hsd : D.cls (gF g (simplePart r.1.1)) = s.2.1)
    (hsc : D.cls (gF g 𝔠) = s.2.2) (l : ℝ) (hl : 0 < l) :
    EA g r (zK K (eU s.1)) 𝔥 (prim 𝔣) * (D.L r.2 (nu g r (zK K (eU s.1))))⁻¹ *
        D.H r.2 (D.cls (nu g r (zK K (eU s.1))))
          ((Ideal.absNorm (zK K (eU s.1)).1.1 : ℝ) / ((Ideal.absNorm r.1.1 : ℝ) ^ 2 * l)) =
      omg g D eU r.2 𝔥 𝔣 𝔞 𝔫 s / (Ideal.absNorm 𝔫 : ℂ) *
        rho g D eU r.2 𝔥 𝔣 𝔞 𝔫 s (simplePart r.1.1) *
        (lam g D eU r.2 𝔥 𝔣 𝔞 𝔫 s 𝔠 * residueSymbol ι 𝔪 (simplePart r.1.1) (g.gen 𝔠) ^ 3 /
          ((Real.sqrt (Ideal.absNorm 𝔠) : ℝ) : ℂ) *
          Hk g D eU r.2 𝔥 𝔣 𝔞 𝔫 s
            (l⁻¹ * Ideal.absNorm 𝔞 * Ideal.absNorm 𝔠 * (Ideal.absNorm 𝔫 : ℝ) ^ 3 /
              ((Ideal.absNorm (simplePart r.1.1) : ℝ) ^ 2 * (Ideal.absNorm 𝔣 : ℝ) ^ 2))) := by
  set u := eU s.1 with hu
  set 𝔡 := simplePart r.1.1 with h𝔡
  set ν := nu g r (zK K u) with hν
  have hprimP : ∀ {P I : Ideal (𝓞 F)}, P ∈ prim I → IsExterior 𝔪 I → P.IsPrime ∧ IsExterior 𝔪 P :=
    fun hP hI => ⟨(prime_of_mem_prim hP).1, exterior_of_prim hI hP⟩
  -- the H-factor
  have hH : D.H r.2 (D.cls ν) ((Ideal.absNorm (zK K u).1.1 : ℝ) / ((Ideal.absNorm r.1.1 : ℝ) ^ 2 * l)) =
      Hk g D eU r.2 𝔥 𝔣 𝔞 𝔫 s
        (l⁻¹ * Ideal.absNorm 𝔞 * Ideal.absNorm 𝔠 * (Ideal.absNorm 𝔫 : ℝ) ^ 3 /
          ((Ideal.absNorm 𝔡 : ℝ) ^ 2 * (Ideal.absNorm 𝔣 : ℝ) ^ 2)) := by
    rw [arg_eq K u l hl, hν, cls_nu g D K u]
    unfold Hk urep
    rw [← hsd, ← hsc, ← hu]
  rw [hH, EA_eval E g K u, phi_prod E g K u, L_nu g D K u]
  -- unfold the coefficients
  have hv1 : IsExterior 𝔪 𝔥 ∧ IsExterior 𝔪 𝔣 ∧ IsExterior 𝔪 𝔞 ∧ IsExterior 𝔪 𝔫 ∧
      (∀ P ∈ normalizedFactors 𝔞, P ∣ 𝔣) ∧ 𝔫 ⊔ 𝔣 = ⊤ :=
    ⟨K.h_ext, K.f_ext, K.ha, K.hn, K.haf, K.hnf⟩
  have hv2 : IsExterior 𝔪 𝔡 ∧ 𝔡 ⊔ 𝔫 = ⊤ ∧ D.cls (gF g 𝔡) = s.2.1 := ⟨K.d_ext, K.hdn, hsd⟩
  have hv3 : IsExterior 𝔪 𝔠 ∧ 𝔠 ⊔ 𝔣 = ⊤ ∧ D.cls (gF g 𝔠) = s.2.2 := ⟨K.hc, K.hcf, hsc⟩
  unfold omg rho lam
  rw [if_pos hv1, if_pos hv2, if_pos hv3]
  -- split the unit-part symbols prime by prime
  set Ur := fun P => uSym g P (urep eU s.1)
  have hur : ((u.rep : SInt 𝔪) : F) = urep eU s.1 := rfl
  have hF : ∀ P ∈ prim 𝔣, sP g 𝔥 P (cnt P 𝔞) * uSym g P ν ^ bP 𝔥 P (cnt P 𝔞) =
      (sP g 𝔥 P (cnt P 𝔞) * (uSym g P (urep eU s.1) * uSym g P (gF g 𝔞) *
          uSym g P (gF g 𝔫) ^ 3 * ((uSym g P (gF g 𝔣))⁻¹) ^ 2) ^ bP 𝔥 P (cnt P 𝔞)) *
        (uSym g P (gF g 𝔠) ^ bP 𝔥 P (cnt P 𝔞) *
          ((uSym g P (gF g 𝔡))⁻¹) ^ (2 * bP 𝔥 P (cnt P 𝔞))) := by
    intro P hP
    obtain ⟨hPp, hPe⟩ := hprimP hP K.f_ext
    rw [hν, uSym_nu E g K u hPp hPe, hur]
    ring
  have hDd : ∀ P ∈ prim 𝔡, om1 g P * uSym g P ν ^ 13 =
      (om1 g P * (uSym g P (urep eU s.1) * uSym g P (gF g 𝔞) * uSym g P (gF g 𝔫) ^ 3 *
          ((uSym g P (gF g 𝔡))⁻¹) ^ 2 * ((uSym g P (gF g 𝔣))⁻¹) ^ 2) ^ 13) *
        uSym g P (gF g 𝔠) ^ 13 := by
    intro P hP
    obtain ⟨hPp, hPe⟩ := hprimP hP K.d_ext
    rw [hν, uSym_nu E g K u hPp hPe, hur]
    ring
  have hC : ∀ Q ∈ prim 𝔠, gaussPhase g 2 Q * uSym g Q ν ^ 2 =
      (gaussPhase g 2 Q * (uSym g Q (urep eU s.1) * uSym g Q (gF g 𝔞) * uSym g Q (gF g 𝔠) *
          ((uSym g Q (gF g 𝔣))⁻¹) ^ 2) ^ 2) * ((uSym g Q (gF g 𝔡))⁻¹) ^ 4 := by
    intro Q hQ
    obtain ⟨hQp, hQe⟩ := hprimP hQ K.hc
    have hn6 : uSym g Q (gF g 𝔫) ^ 6 = 1 :=
      uSym_pow_sixE E g hQp hQe (C3B.gen_ne_zero g _ K.hn)
    rw [hν, uSym_nu E g K u hQp hQe, hur]
    have : (uSym g Q (urep eU s.1) * uSym g Q (gF g 𝔞) * uSym g Q (gF g 𝔠) *
        uSym g Q (gF g 𝔫) ^ 3 * ((uSym g Q (gF g 𝔡))⁻¹) ^ 2 * ((uSym g Q (gF g 𝔣))⁻¹) ^ 2) ^ 2 =
        (uSym g Q (urep eU s.1) * uSym g Q (gF g 𝔞) * uSym g Q (gF g 𝔠) *
          ((uSym g Q (gF g 𝔣))⁻¹) ^ 2) ^ 2 * uSym g Q (gF g 𝔫) ^ 6 *
          ((uSym g Q (gF g 𝔡))⁻¹) ^ 4 := by ring
    rw [this, hn6]
    ring
  rw [Finset.prod_congr rfl hF, Finset.prod_congr rfl hDd, Finset.prod_congr rfl hC]
  simp only [Finset.prod_mul_distrib]
  have hpair := pairing E g K
  have hpair' : (∏ P ∈ prim 𝔡, uSym g P (gF g 𝔠) ^ 13) * (∏ Q ∈ prim 𝔠,
      ((uSym g Q (gF g 𝔡))⁻¹) ^ 4) = residueSymbol ι 𝔪 𝔡 (g.gen 𝔠) ^ 3 := hpair
  rw [← hpair']
  have hn0 : (Ideal.absNorm 𝔫 : ℂ) ≠ 0 := by
    have := absNorm_pos_real K.hn.1
    exact_mod_cast this.ne'
  have hc0 : (((Real.sqrt (Ideal.absNorm 𝔠)) : ℝ) : ℂ) ≠ 0 := by
    have := absNorm_pos_real K.hc.1
    exact_mod_cast (Real.sqrt_pos.2 this).ne'
  simp only [div_eq_mul_inv]
  ring

end L3V

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3V_Bij: the frequency parametrization (6.21) for one active set `𝔣`

For fixed `r`, `𝔥 = 𝔣 𝔤`, the map `Ψ : (𝔞′, 𝔫′, s, 𝔠′) ↦ (𝔤² 𝔞′ 𝔠′ 𝔫′³, u)` is injective on the valid
keys (`Psi_inj`), every frequency with `E_{prim 𝔣}(ν) ≠ 0` is in its image (`supp_sub`), and the
summands agree (`FA_Psi`); off the valid keys Cut63V's summand vanishes (`Gp_eq_zero`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-- The non-active coordinates of a key, with the column. -/
abbrev Rst {g : AllowedGen ι 𝔪} {χ : HeckeChar F 𝔪} (D : Data χ g) (N : ℕ) : Type _ :=
  {𝔞 : Ideal (𝓞 F) // 𝔞 ≠ ⊥} × {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫} × TT D N ×
    {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠}

section

variable (g : AllowedGen ι 𝔪) {χ : HeckeChar F 𝔪} (D : Data χ g) {N : ℕ}
  (eU : Fin N ≃ SClass 𝔪) (r : RowClass 𝔪) (𝔥 𝔣 𝔤 : Ideal (𝓞 F)) (l : ℝ)

/-- Cut63V's joint summand at `(𝔣, b)`. -/
noncomputable def Gp (b : Rst D N) : ℂ :=
  omg g D eU r.2 𝔥 𝔣 b.1.1 b.2.1.1 b.2.2.1 / (Ideal.absNorm b.2.1.1 : ℂ) *
    rho g D eU r.2 𝔥 𝔣 b.1.1 b.2.1.1 b.2.2.1 (simplePart r.1.1) *
    (lam g D eU r.2 𝔥 𝔣 b.1.1 b.2.1.1 b.2.2.1 b.2.2.2.1 *
      residueSymbol ι 𝔪 (simplePart r.1.1) (g.gen b.2.2.2.1) ^ 3 /
        ((Real.sqrt (Ideal.absNorm b.2.2.2.1) : ℝ) : ℂ) *
      Hk g D eU r.2 𝔥 𝔣 b.1.1 b.2.1.1 b.2.2.1
        (l⁻¹ * Ideal.absNorm b.1.1 * Ideal.absNorm b.2.2.2.1 * (Ideal.absNorm b.2.1.1 : ℝ) ^ 3 /
          ((Ideal.absNorm (simplePart r.1.1) : ℝ) ^ 2 * (Ideal.absNorm 𝔣 : ℝ) ^ 2)))

/-- The valid keys. -/
def Valid (b : Rst D N) : Prop :=
  IsExterior 𝔪 b.1.1 ∧ (∀ P ∈ normalizedFactors b.1.1, P ∣ 𝔣) ∧ b.2.1.1 ⊔ 𝔣 = ⊤ ∧
    simplePart r.1.1 ⊔ b.2.1.1 = ⊤ ∧ D.cls (gF g (simplePart r.1.1)) = b.2.2.1.2.1 ∧
    b.2.2.2.1 ⊔ 𝔣 = ⊤ ∧ D.cls (gF g b.2.2.2.1) = b.2.2.1.2.2 ∧
    b.2.2.2.1 ⊔ simplePart r.1.1 = ⊤

open Classical in
/-- `Ψ(b) = (𝔤² 𝔞′ 𝔠′ 𝔫′³, u)`. -/
noncomputable def Psi (b : Rst D N) : RowClass 𝔪 :=
  if h : IsExterior 𝔪 (xI 𝔤 b.1.1 b.2.1.1 b.2.2.2.1) then (⟨_, h⟩, eU b.2.2.1.1)
  else (⟨⊤, ⟨top_ne_bot, top_sup_eq _⟩⟩, eU b.2.2.1.1)

/-- The `prim 𝔣`-part of the cut's summand. -/
noncomputable def FA (z : RowClass 𝔪) : ℂ :=
  EA g r z 𝔥 (prim 𝔣) * (D.L r.2 (nu g r z))⁻¹ *
    D.H r.2 (D.cls (nu g r z)) ((Ideal.absNorm z.1.1 : ℝ) / ((Ideal.absNorm r.1.1 : ℝ) ^ 2 * l))

end

variable (E : Env ι 𝔪) (g : AllowedGen ι 𝔪) {χ : HeckeChar F 𝔪} (D : Data χ g) {N : ℕ}
  (eU : Fin N ≃ SClass 𝔪) (r : RowClass 𝔪) {𝔥 𝔣 𝔤 : Ideal (𝓞 F)} (l : ℝ)

/-- The key hypotheses for a valid key. -/
lemma keyHyp_of_valid (h𝔥 : 𝔥 * simplePart r.1.1 = r.1.1) (hfg : 𝔥 = 𝔣 * 𝔤)
    (h𝔣 : Squarefree 𝔣 ∧ 𝔣 * 𝔣 ∣ 𝔥) {b : Rst D N} (hb : Valid g D r 𝔣 b) :
    KeyHyp r 𝔥 𝔣 𝔤 b.1.1 b.2.1.1 b.2.2.2.1 :=
  ⟨h𝔥, hfg, h𝔣.1, h𝔣.2, hb.1, hb.2.1, b.2.1.2, hb.2.2.1, hb.2.2.2.1, b.2.2.2.2.1, b.2.2.2.2.2,
    hb.2.2.2.2.2.1, hb.2.2.2.2.2.2.2⟩

lemma Psi_valid (h𝔥 : 𝔥 * simplePart r.1.1 = r.1.1) (hfg : 𝔥 = 𝔣 * 𝔤)
    (h𝔣 : Squarefree 𝔣 ∧ 𝔣 * 𝔣 ∣ 𝔥) {b : Rst D N} (hb : Valid g D r 𝔣 b) :
    Psi g D eU 𝔤 b = zK (keyHyp_of_valid g D r h𝔥 hfg h𝔣 hb) (eU b.2.2.1.1) := by
  unfold Psi
  rw [dif_pos (keyHyp_of_valid g D r h𝔥 hfg h𝔣 hb).x_ext]

include E in
lemma FA_Psi (h𝔥 : 𝔥 * simplePart r.1.1 = r.1.1) (hfg : 𝔥 = 𝔣 * 𝔤)
    (h𝔣 : Squarefree 𝔣 ∧ 𝔣 * 𝔣 ∣ 𝔥) (hl : 0 < l) {b : Rst D N} (hb : Valid g D r 𝔣 b) :
    FA g D r 𝔥 𝔣 l (Psi g D eU 𝔤 b) = Gp g D eU r 𝔥 𝔣 l b := by
  have K := keyHyp_of_valid g D r h𝔥 hfg h𝔣 hb
  rw [Psi_valid g D eU r h𝔥 hfg h𝔣 hb]
  unfold FA Gp
  exact key_identity E g D eU K b.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2.2.1 l hl

include E in
lemma Gp_eq_zero (h𝔥 : 𝔥 * simplePart r.1.1 = r.1.1) (hfg : 𝔥 = 𝔣 * 𝔤)
    (h𝔣 : Squarefree 𝔣 ∧ 𝔣 * 𝔣 ∣ 𝔥) {b : Rst D N} (hb : ¬ Valid g D r 𝔣 b) :
    Gp g D eU r 𝔥 𝔣 l b = 0 := by
  have h𝔟 : r.1.1 ≠ ⊥ := r.1.2.1
  have hhe : IsExterior 𝔪 𝔥 := C3M.isExterior_of_mul_left (h𝔥.symm ▸ r.1.2)
  have hfe : IsExterior 𝔪 𝔣 := C3M.isExterior_of_mul_left (hfg ▸ hhe)
  unfold Valid at hb
  unfold Gp
  by_cases h1 : IsExterior 𝔪 b.1.1 ∧ (∀ P ∈ normalizedFactors b.1.1, P ∣ 𝔣) ∧ b.2.1.1 ⊔ 𝔣 = ⊤
  · by_cases h2 : simplePart r.1.1 ⊔ b.2.1.1 = ⊤ ∧
        D.cls (gF g (simplePart r.1.1)) = b.2.2.1.2.1
    · by_cases h3 : b.2.2.2.1 ⊔ 𝔣 = ⊤ ∧ D.cls (gF g b.2.2.2.1) = b.2.2.1.2.2
      · -- the column meets the row
        have h4 : ¬ b.2.2.2.1 ⊔ simplePart r.1.1 = ⊤ := by tauto
        have hz : residueSymbol ι 𝔪 (simplePart r.1.1) (g.gen b.2.2.2.1) = 0 := by
          have hc := b.2.2.2.2.1
          have hd : simplePart r.1.1 ≠ ⊥ := L2D_simplePart_ne_bot _ h𝔟
          rw [sup_eq_top_iff_cnt hc.1 hd] at h4
          push Not at h4
          obtain ⟨P, hPc, hPd⟩ := h4
          have hPm : P ∈ normalizedFactors (simplePart r.1.1) := Multiset.count_ne_zero.1 hPd
          unfold residueSymbol
          apply Multiset.prod_eq_zero
          refine Multiset.mem_map.2 ⟨P, hPm, ?_⟩
          unfold sexticResidueSymbol
          rw [if_pos]
          rw [Ideal.Quotient.eq_zero_iff_mem]
          have hmem : g.gen b.2.2.2.1 ∈ b.2.2.2.1.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
            rw [← g.span_gen _ hc]; exact Ideal.mem_span_singleton_self _
          have hle : b.2.2.2.1 ≤ P := by
            have hp := L2D_prime_of_mem hPm
            rw [← Ideal.dvd_iff_le, dvd_iff_cnt_pos (Ideal.isPrime_of_prime hp) hp.ne_zero hc.1]
            omega
          exact Ideal.map_mono hle hmem
        rw [hz]; simp
      · have : lam g D eU r.2 𝔥 𝔣 b.1.1 b.2.1.1 b.2.2.1 b.2.2.2.1 = 0 := by
          unfold lam; rw [if_neg]; rintro ⟨-, h, h'⟩; exact h3 ⟨h, h'⟩
        rw [this]; simp
    · have : rho g D eU r.2 𝔥 𝔣 b.1.1 b.2.1.1 b.2.2.1 (simplePart r.1.1) = 0 := by
        unfold rho; rw [if_neg]; rintro ⟨-, h, h'⟩; exact h2 ⟨h, h'⟩
      rw [this]; simp
  · have : omg g D eU r.2 𝔥 𝔣 b.1.1 b.2.1.1 b.2.2.1 = 0 := by
      unfold omg; rw [if_neg]; rintro ⟨-, -, ha, -, haf, hnf⟩; exact h1 ⟨ha, haf, hnf⟩
    rw [this]; simp

lemma Psi_inj (h𝔥 : 𝔥 * simplePart r.1.1 = r.1.1) (hfg : 𝔥 = 𝔣 * 𝔤)
    (h𝔣 : Squarefree 𝔣 ∧ 𝔣 * 𝔣 ∣ 𝔥) {b b' : Rst D N} (hb : Valid g D r 𝔣 b)
    (hb' : Valid g D r 𝔣 b') (he : Psi g D eU 𝔤 b = Psi g D eU 𝔤 b') : b = b' := by
  have K := keyHyp_of_valid g D r h𝔥 hfg h𝔣 hb
  have K' := keyHyp_of_valid g D r h𝔥 hfg h𝔣 hb'
  rw [Psi_valid g D eU r h𝔥 hfg h𝔣 hb, Psi_valid g D eU r h𝔥 hfg h𝔣 hb'] at he
  have hx : xI 𝔤 b.1.1 b.2.1.1 b.2.2.2.1 = xI 𝔤 b'.1.1 b'.2.1.1 b'.2.2.2.1 :=
    congrArg (fun z : RowClass 𝔪 => z.1.1) he
  have hu : b.2.2.1.1 = b'.2.2.1.1 := eU.injective (congrArg Prod.snd he)
  -- exponents
  have hcnt : ∀ P, cnt P b.1.1 = cnt P b'.1.1 ∧ cnt P b.2.2.2.1 = cnt P b'.2.2.2.1 ∧
      cnt P b.2.1.1 = cnt P b'.2.1.1 := by
    intro P
    have h1 := K.cnt_x P
    have h2 := K'.cnt_x P
    rw [hx] at h1
    have hc := K.cnt_c_le P
    have hc' := K'.cnt_c_le P
    by_cases hf : cnt P 𝔣 = 0
    · have ha := K.cnt_a_of hf
      have ha' := K'.cnt_a_of hf
      refine ⟨by omega, by omega, by omega⟩
    · have hc0 : cnt P b.2.2.2.1 = 0 := by
        rcases K.cop_cnt K.hc.1 K.f_ext.1 K.hcf P with h | h <;> [exact h; omega]
      have hc0' : cnt P b'.2.2.2.1 = 0 := by
        rcases K'.cop_cnt K'.hc.1 K'.f_ext.1 K'.hcf P with h | h <;> [exact h; omega]
      have hn0 : cnt P b.2.1.1 = 0 := by
        rcases K.cop_cnt K.hn.1 K.f_ext.1 K.hnf P with h | h <;> [exact h; omega]
      have hn0' : cnt P b'.2.1.1 = 0 := by
        rcases K'.cop_cnt K'.hn.1 K'.f_ext.1 K'.hnf P with h | h <;> [exact h; omega]
      refine ⟨by omega, by omega, by omega⟩
  have ea : b.1.1 = b'.1.1 := eq_of_cnt K.ha.1 K'.ha.1 fun P _ _ => (hcnt P).1
  have ec : b.2.2.2.1 = b'.2.2.2.1 := eq_of_cnt K.hc.1 K'.hc.1 fun P _ _ => (hcnt P).2.1
  have en : b.2.1.1 = b'.2.1.1 := eq_of_cnt K.hn.1 K'.hn.1 fun P _ _ => (hcnt P).2.2
  have hsd : b.2.2.1.2.1 = b'.2.2.1.2.1 := hb.2.2.2.2.1.symm.trans hb'.2.2.2.2.1
  have hsc : b.2.2.1.2.2 = b'.2.2.1.2.2 := by
    rw [← hb.2.2.2.2.2.2.1, ← hb'.2.2.2.2.2.2.1, ec]
  obtain ⟨⟨a, ha⟩, ⟨n, hn⟩, ⟨u, sd, sc⟩, ⟨c, hc⟩⟩ := b
  obtain ⟨⟨a', ha'⟩, ⟨n', hn'⟩, ⟨u', sd', sc'⟩, ⟨c', hc'⟩⟩ := b'
  simp only at ea ec en hu hsd hsc
  subst ea ec en hu hsd hsc
  rfl

end L3V

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3V_Supp: every frequency with `E_{prim 𝔣}(ν) ≠ 0` comes from a valid key

`supp_sub`: if `FA z ≠ 0` then `z = Ψ(b)` for a valid key `b`. The local vanishing gives
`v_𝔭(ν) ≥ −2` at `𝔭 ∣ 𝔣`, `v_𝔭(ν) ≥ 0`, `≢ 2 (mod 3)` at inactive and exterior primes, and
`v_𝔭(ν) = −2` at `𝔭 ∣ 𝔡` ((6.14)); the key is read off from the exponents (the paper's sentence
after (6.21): "the valuations `3k` and `3k+1` determine `𝔠′` and `𝔫′` uniquely").
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

lemma Wsph_ne_zero_imp {g : AllowedGen ι 𝔪} {P : Ideal (𝓞 F)} {e : ℤ} {t : F}
    (h : Wsph g P e t ≠ 0) : 0 ≤ e ∧ e.toNat % 3 ≠ 2 := by
  unfold Wsph at h
  split_ifs at h with he
  · exact absurd rfl h
  · refine ⟨by omega, fun h2 => h ?_⟩
    unfold Wv; rw [if_neg (by omega), if_neg (by omega), mul_zero]

lemma Rsum_ne_zero_imp {g : AllowedGen ι 𝔪} {P : Ideal (𝓞 F)} {j : ℕ} {e : ℤ} {t : F}
    (h : Rsum g P j e t ≠ 0) : 0 ≤ e + 2 := by
  by_contra hc
  push Not at hc
  apply h
  unfold Rsum Wweyl
  simp [hc]

variable (E : Env ι 𝔪) (g : AllowedGen ι 𝔪) {χ : HeckeChar F 𝔪} (D : Data χ g) {N : ℕ}
  (eU : Fin N ≃ SClass 𝔪) (r : RowClass 𝔪) {𝔥 𝔣 𝔤 : Ideal (𝓞 F)} (l : ℝ)

include E in
lemma Rsum1_ne_zero_imp {P : Ideal (𝓞 F)} (hP : P.IsPrime) (he : IsExterior 𝔪 P) (z : RowClass 𝔪)
    (h : Rsum g P 1 (e0 r z P) (tz g r z P) ≠ 0) : e0 r z P = -2 := by
  have h0 := Rsum_ne_zero_imp h
  by_contra hne
  have hpos : 0 < e0 r z P + 2 := by omega
  have hval : (⟨P, hP, he.1⟩ : HeightOneSpectrum (𝓞 F)).valuation F (tz g r z P) ≤ 1 := by
    rw [tz_eq g r z P (vP_nu E g hP he r z)]
    exact (val_unitPartE E g hP he (nu_ne_zero g r z)).le
  exact h ((E.loc g P hP he).Rsum_one _ hpos _ hval)

include E in
lemma supp_sub (h𝔥 : 𝔥 * simplePart r.1.1 = r.1.1) (hfg : 𝔥 = 𝔣 * 𝔤)
    (h𝔣 : Squarefree 𝔣 ∧ 𝔣 * 𝔣 ∣ 𝔥) (z : RowClass 𝔪) (hz : FA g D r 𝔥 𝔣 l z ≠ 0) :
    ∃ b : Rst D N, Valid g D r 𝔣 b ∧ Psi g D eU 𝔤 b = z := by
  classical
  set 𝔡 := simplePart r.1.1 with h𝔡
  set 𝔵 := z.1.1 with h𝔵
  have h𝔟 : r.1.1 ≠ ⊥ := r.1.2.1
  have hx0 : 𝔵 ≠ ⊥ := z.1.2.1
  have hhe : IsExterior 𝔪 𝔥 := C3M.isExterior_of_mul_left (h𝔥.symm ▸ r.1.2)
  have hde : IsExterior 𝔪 𝔡 := C3M.isExterior_of_mul_right (h𝔥.symm ▸ r.1.2)
  have hfe : IsExterior 𝔪 𝔣 := C3M.isExterior_of_mul_left (hfg ▸ hhe)
  have hge : IsExterior 𝔪 𝔤 := C3M.isExterior_of_mul_right (hfg ▸ hhe)
  have hxb : IsExterior 𝔪 (𝔵 * r.1.1) := C3I.isExterior_mul z.1.2 r.1.2
  obtain ⟨hrow, hdisj⟩ := prim_row h𝔟 h𝔥
  have hcntb : ∀ P, cnt P r.1.1 = cnt P 𝔣 + cnt P 𝔤 + cnt P 𝔡 := fun P => by
    rw [cnt_row h𝔟 h𝔥, hfg, cnt_mul hfe.1 hge.1]
  have hcnth : ∀ P, cnt P 𝔥 = cnt P 𝔣 + cnt P 𝔤 := fun P => by rw [hfg, cnt_mul hfe.1 hge.1]
  have hcntxb : ∀ P, cnt P (𝔵 * r.1.1) = cnt P 𝔵 + cnt P r.1.1 := fun P => cnt_mul hx0 h𝔟
  have he0 : ∀ P, e0 r z P = (cnt P 𝔵 : ℤ) - 2 * (cnt P r.1.1 : ℤ) := fun P => rfl
  have hf1 : ∀ P ∈ prim 𝔣, cnt P 𝔣 = 1 := fun P hP =>
    le_antisymm ((squarefree_iff_cnt hfe.1).1 h𝔣.1 P) (mem_prim_iff.1 hP)
  have hfh : prim 𝔣 ⊆ prim 𝔥 := fun P hP => by
    rw [mem_prim_iff] at hP ⊢; rw [hcnth]; omega
  have hd0h : ∀ P ∈ prim 𝔥, cnt P 𝔡 = 0 := fun P hP => (cnt_h_of_mem h𝔟 h𝔥 hP).2.1
  have hh0d : ∀ P ∈ prim 𝔡, cnt P 𝔥 = 0 := fun P hP => (cnt_d_of_mem h𝔟 h𝔥 hP).1
  -- the local nonvanishing
  have hEA : EA g r z 𝔥 (prim 𝔣) ≠ 0 := by
    intro h0; apply hz; unfold FA; rw [h0, zero_mul, zero_mul]
  unfold EA at hEA
  have hP1 := left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hEA))
  have hP2 := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hEA))
  have hP3 := right_ne_zero_of_mul (left_ne_zero_of_mul hEA)
  have hP4 := right_ne_zero_of_mul hEA
  rw [Finset.prod_ne_zero_iff] at hP1 hP2 hP3 hP4
  have iA : ∀ P ∈ prim 𝔣, 0 ≤ e0 r z P + 2 := fun P hP => Rsum_ne_zero_imp (hP1 P hP)
  have iB : ∀ P ∈ prim 𝔥 \ prim 𝔣, 0 ≤ e0 r z P ∧ (e0 r z P).toNat % 3 ≠ 2 := fun P hP =>
    Wsph_ne_zero_imp (right_ne_zero_of_mul (hP2 P hP))
  have iC : ∀ P ∈ prim 𝔡, e0 r z P = -2 := fun P hP => by
    have hm : P ∈ prim r.1.1 := hrow ▸ Finset.mem_union_right _ hP
    exact Rsum1_ne_zero_imp E g r (prime_of_mem_prim hm).1 (exterior_of_prim r.1.2 hm) z
      (hP3 P hP)
  have iD : ∀ P ∈ prim (𝔵 * r.1.1) \ prim r.1.1, 0 ≤ e0 r z P ∧ (e0 r z P).toNat % 3 ≠ 2 :=
    fun P hP => Wsph_ne_zero_imp (hP4 P hP)
  -- the key
  set S := (prim 𝔥 \ prim 𝔣) ∪ (prim (𝔵 * r.1.1) \ prim r.1.1) with hS
  have hSpr : ∀ P ∈ S, P.IsPrime ∧ P ≠ ⊥ := by
    intro P hP
    rcases Finset.mem_union.1 hP with h | h
    · exact prime_of_mem_prim (Finset.mem_sdiff.1 h).1
    · exact prime_of_mem_prim (Finset.mem_sdiff.1 h).1
  have hSex : ∀ P ∈ S, IsExterior 𝔪 P := by
    intro P hP
    rcases Finset.mem_union.1 hP with h | h
    · exact exterior_of_prim hhe (Finset.mem_sdiff.1 h).1
    · exact exterior_of_prim hxb (Finset.mem_sdiff.1 h).1
  have hSf : ∀ P ∈ S, cnt P 𝔣 = 0 := by
    intro P hP
    rcases Finset.mem_union.1 hP with h | h
    · have := (Finset.mem_sdiff.1 h).2; rw [mem_prim_iff] at this; omega
    · have := (Finset.mem_sdiff.1 h).2; rw [mem_prim_iff, hcntb] at this; omega
  have hSd : ∀ P ∈ S, cnt P 𝔡 = 0 := by
    intro P hP
    rcases Finset.mem_union.1 hP with h | h
    · exact hd0h P (Finset.mem_sdiff.1 h).1
    · have := (Finset.mem_sdiff.1 h).2; rw [mem_prim_iff, hcntb] at this; omega
  have hfpr : ∀ P ∈ prim 𝔣, P.IsPrime ∧ P ≠ ⊥ := fun P hP => prime_of_mem_prim hP
  set aE : Ideal (𝓞 F) → ℕ := fun P => (e0 r z P + 2).toNat
  set yE : Ideal (𝓞 F) → ℕ := fun P => (e0 r z P).toNat
  set 𝔞 := ∏ P ∈ prim 𝔣, P ^ aE P with h𝔞
  set Sc := S.filter (fun P => yE P % 3 = 1) with hSc
  set 𝔠 := ∏ P ∈ Sc, P ^ (1 : ℕ) with h𝔠
  set 𝔫 := ∏ P ∈ S, P ^ (yE P / 3) with h𝔫
  have hScS : Sc ⊆ S := Finset.filter_subset _ _
  have ca : ∀ P, cnt P 𝔞 = if P ∈ prim 𝔣 then aE P else 0 := fun P =>
    cnt_prod_pow P _ hfpr aE
  have cc : ∀ P, cnt P 𝔠 = if P ∈ Sc then 1 else 0 := fun P =>
    cnt_prod_pow P _ (fun Q hQ => hSpr Q (hScS hQ)) (fun _ => 1)
  have cn : ∀ P, cnt P 𝔫 = if P ∈ S then yE P / 3 else 0 := fun P =>
    cnt_prod_pow P _ hSpr (fun Q => yE Q / 3)
  have ha : IsExterior 𝔪 𝔞 := exterior_prod_pow _ (fun P hP => exterior_of_prim hfe hP) _
  have hc : IsExterior 𝔪 𝔠 := exterior_prod_pow _ (fun P hP => hSex P (hScS hP)) _
  have hn : IsExterior 𝔪 𝔫 := exterior_prod_pow _ hSex _
  have hcs : Squarefree 𝔠 := by
    rw [squarefree_iff_cnt hc.1]; intro P; rw [cc]; split_ifs <;> omega
  have topcnt : ∀ {I J : Ideal (𝓞 F)}, I ≠ ⊥ → J ≠ ⊥ → (∀ P, cnt P I = 0 ∨ cnt P J = 0) →
      I ⊔ J = ⊤ := fun hI hJ h => (sup_eq_top_iff_cnt hI hJ).2 h
  have hnf : 𝔫 ⊔ 𝔣 = ⊤ := topcnt hn.1 hfe.1 fun P => by
    rw [cn]; by_cases hP : P ∈ S
    · right; exact hSf P hP
    · left; rw [if_neg hP]
  have hdn : 𝔡 ⊔ 𝔫 = ⊤ := topcnt hde.1 hn.1 fun P => by
    rw [cn]; by_cases hP : P ∈ S
    · left; exact hSd P hP
    · right; rw [if_neg hP]
  have hcf : 𝔠 ⊔ 𝔣 = ⊤ := topcnt hc.1 hfe.1 fun P => by
    rw [cc]; by_cases hP : P ∈ Sc
    · right; exact hSf P (hScS hP)
    · left; rw [if_neg hP]
  have hcd : 𝔠 ⊔ 𝔡 = ⊤ := topcnt hc.1 hde.1 fun P => by
    rw [cc]; by_cases hP : P ∈ Sc
    · right; exact hSd P (hScS hP)
    · left; rw [if_neg hP]
  have haf : ∀ P ∈ normalizedFactors 𝔞, P ∣ 𝔣 := by
    intro P hP
    have hpos : 0 < cnt P 𝔞 := Multiset.count_pos.2 hP
    rw [ca] at hpos
    split_ifs at hpos with hPf
    · exact dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.1 hPf)
    · omega
  let b : Rst D N := (⟨𝔞, ha.1⟩, ⟨𝔫, hn⟩, (eU.symm z.2, D.cls (gF g 𝔡), D.cls (gF g 𝔠)),
    ⟨𝔠, hc, hcs⟩)
  have hb : Valid g D r 𝔣 b := ⟨ha, haf, hnf, hdn, rfl, hcf, rfl, hcd⟩
  refine ⟨b, hb, ?_⟩
  rw [Psi_valid g D eU r h𝔥 hfg h𝔣 hb]
  have K := keyHyp_of_valid g D r h𝔥 hfg h𝔣 hb
  apply Prod.ext
  · apply Subtype.ext
    change xI 𝔤 𝔞 𝔫 𝔠 = 𝔵
    apply eq_of_cnt K.x_ext.1 hx0
    intro P _ _
    rw [K.cnt_x P]
    change 2 * cnt P 𝔤 + cnt P 𝔞 + cnt P 𝔠 + 3 * cnt P 𝔫 = cnt P 𝔵
    rw [ca, cc, cn]
    have hb' := hcntb P
    have hxb' := hcntxb P
    have he := he0 P
    by_cases hPf : P ∈ prim 𝔣
    · have h1 := hf1 P hPf
      have hd := hd0h P (hfh hPf)
      have hPS : P ∉ S := fun h => by have := hSf P h; omega
      have hPSc : P ∉ Sc := fun h => hPS (hScS h)
      have hA := iA P hPf
      rw [if_pos hPf, if_neg hPSc, if_neg hPS]
      change 2 * cnt P 𝔤 + (e0 r z P + 2).toNat + 0 + 3 * 0 = cnt P 𝔵
      omega
    · have hf0 : cnt P 𝔣 = 0 := by rw [mem_prim_iff] at hPf; omega
      rw [if_neg hPf]
      by_cases hPS : P ∈ S
      · have hPy : (e0 r z P).toNat % 3 ≠ 2 ∧ 0 ≤ e0 r z P ∧ cnt P 𝔤 = cnt P r.1.1 := by
          rcases Finset.mem_union.1 hPS with h | h
          · have := iB P h
            have hd := hd0h P (Finset.mem_sdiff.1 h).1
            exact ⟨this.2, this.1, by omega⟩
          · have := iD P h
            have h0 := (Finset.mem_sdiff.1 h).2
            rw [mem_prim_iff] at h0
            exact ⟨this.2, this.1, by omega⟩
        rw [if_pos hPS]
        by_cases hPc : P ∈ Sc
        · rw [if_pos hPc]
          have hy1 : (e0 r z P).toNat % 3 = 1 := (Finset.mem_filter.1 hPc).2
          change 2 * cnt P 𝔤 + 0 + 1 + 3 * ((e0 r z P).toNat / 3) = cnt P 𝔵
          omega
        · rw [if_neg hPc]
          have hy0 : (e0 r z P).toNat % 3 ≠ 1 := fun h => hPc (Finset.mem_filter.2 ⟨hPS, h⟩)
          change 2 * cnt P 𝔤 + 0 + 0 + 3 * ((e0 r z P).toNat / 3) = cnt P 𝔵
          omega
      · have hPSc : P ∉ Sc := fun h => hPS (hScS h)
        rw [if_neg hPSc, if_neg hPS]
        -- `P` is a prime of `𝔡`, or outside `𝔵 𝔟`
        by_cases hPd : P ∈ prim 𝔡
        · have := iC P hPd
          have hh := hh0d P hPd
          have := hcnth P
          have hd1 := (cnt_d_of_mem h𝔟 h𝔥 hPd).2
          omega
        · have hPh : P ∉ prim 𝔥 := fun h => hPS (Finset.mem_union_left _
            (Finset.mem_sdiff.2 ⟨h, hPf⟩))
          have hPb : P ∉ prim r.1.1 := by
            rw [hrow, Finset.mem_union, not_or]; exact ⟨hPh, hPd⟩
          have hPxb : P ∉ prim (𝔵 * r.1.1) := fun h => hPS (Finset.mem_union_right _
            (Finset.mem_sdiff.2 ⟨h, hPb⟩))
          rw [mem_prim_iff] at hPh hPb hPxb
          have := hcnth P
          omega
  · exact eU.apply_symm_apply z.2

end L3V

end ArtinPrimitiveRoots

end
end

section
section
namespace ArtinPrimitiveRoots

open MeasureTheory Real
open scoped FourierTransform RealInnerProductSpace

/-! L2D: Fourier separation of a profile in the log variable ((5.19), (6.43), simplified). -/

end ArtinPrimitiveRoots

end
end

section
section
namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

/-! L2D core, part 1: the data of Cut63 for fixed `𝔪, χ, g`, and the elementary bounds. -/

variable {F : Type*} [Field F] [NumberField F]

/-! ### Elementary bounds -/

lemma L2D_norm_sext_le (ι : F →+* ℂ) (𝔪 P : Ideal (𝓞 F)) (x : SInt 𝔪) :
    ‖sexticResidueSymbol ι 𝔪 P x‖ ≤ 1 := by
  unfold sexticResidueSymbol
  split_ifs with h1 h2
  · simp
  · have h6 : (ι (h2.choose : F)) ^ 6 = 1 := by
      rw [← map_pow, ← map_pow]
      have := h2.choose_spec.1
      rw [this]
      simp
    rw [Complex.norm_eq_one_of_pow_eq_one h6 (by norm_num)]
  · simp

lemma L2D_norm_residueSymbol_le (ι : F →+* ℂ) (𝔪 𝔞 : Ideal (𝓞 F)) (x : SInt 𝔪) :
    ‖residueSymbol ι 𝔪 𝔞 x‖ ≤ 1 := by
  unfold residueSymbol
  induction (normalizedFactors 𝔞) using Multiset.induction_on with
  | empty => simp
  | cons P s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    exact mul_le_one₀ (L2D_norm_sext_le ι 𝔪 P x) (norm_nonneg _) ih

lemma L2D_one_le_absNorm {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : (1 : ℝ) ≤ Ideal.absNorm I := by
  have : Ideal.absNorm I ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  exact_mod_cast Nat.one_le_iff_ne_zero.2 this

/-- From (6.22) with `j = 0`: `|Φ(x)| ≤ C x^{-N}` for `x > 0`. -/
lemma L2D_Phi_le {Φ : ℝ → ℂ} {α N C : ℝ}
    (hb : ∀ t : ℝ, ‖Φ (Real.exp t)‖ ≤ C * min (Real.exp (α * t)) (Real.exp (-(N * t))))
    {x : ℝ} (hx : 0 < x) : ‖Φ x‖ ≤ C * x ^ (-N) := by
  have h := hb (Real.log x)
  rw [Real.exp_log hx] at h
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans h
    by_contra hneg; push Not at hneg
    have : 0 < min (Real.exp (α * Real.log x)) (Real.exp (-(N * Real.log x))) :=
      lt_min (Real.exp_pos _) (Real.exp_pos _)
    nlinarith
  calc ‖Φ x‖ ≤ C * min (Real.exp (α * Real.log x)) (Real.exp (-(N * Real.log x))) := h
    _ ≤ C * Real.exp (-(N * Real.log x)) := by gcongr; exact min_le_right _ _
    _ = C * x ^ (-N) := by
        rw [Real.rpow_def_of_pos hx]; congr 1; ring_nf

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3V_Sum1: absolute convergence and the per-`𝔣` reindexing

* `H_le`: `|H(y)| ≤ C/y` (from (5.17) with `N = 1`);
* `norm_Gp_le`: `|Gp| ≤ C l N𝔡² N𝔣² β_𝔣(𝔞′) N𝔫′^{−4} N𝔠′^{−3/2}`;
* `summable_Gp`, and `tsum_FA`: `∑'_x E_{prim 𝔣}(x/b²)… = ∑'_b Gp(𝔣, b)` through `Ψ`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

lemma H_le {g : AllowedGen ι 𝔪} {χ : HeckeChar F 𝔪} (D : Data χ g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ υ κ (y : ℝ), 0 < y → ‖D.H υ κ y‖ ≤ C * y⁻¹ := by
  obtain ⟨C, hC⟩ := D.hHb 1 one_pos
  have hb : ∀ υ κ (t : ℝ), ‖D.H υ κ (Real.exp t)‖ ≤
      C * min (Real.exp (D.α * t)) (Real.exp (-(1 * t))) := by
    intro υ κ t
    have := hC υ κ 0 (by norm_num) t
    simpa using this
  have hC0 : 0 ≤ C := by
    have h := hb (Classical.arbitrary _) (Classical.arbitrary _) 0
    have := (norm_nonneg _).trans h
    simp at this
    linarith
  refine ⟨C, hC0, fun υ κ y hy => ?_⟩
  have := L2D_Phi_le (hb υ κ) hy
  rw [Real.rpow_neg_one] at this
  exact this

variable (E : Env ι 𝔪) (g : AllowedGen ι 𝔪) {χ : HeckeChar F 𝔪} (D : Data χ g) {N : ℕ}
  (eU : Fin N ≃ SClass 𝔪) (r : RowClass 𝔪) {𝔥 𝔣 𝔤 : Ideal (𝓞 F)} (l : ℝ)

include E in
lemma norm_omg_le' (υ : SClass 𝔪) (𝔞 𝔫 : Ideal (𝓞 F)) (s : TT D N) :
    ‖omg g D eU υ 𝔥 𝔣 𝔞 𝔫 s‖ ≤ L2D_beta 𝔣 𝔞 := by
  classical
  unfold L2D_beta
  split_ifs with h
  · exact norm_omg_le E g D eU υ 𝔥 𝔣 𝔞 𝔫 s
  · push Not at h
    rw [omg_eq_zero g D eU υ 𝔥 𝔣 𝔞 𝔫 s h, norm_zero]

/-- The weight bounding `Gp`. -/
noncomputable def wt (𝔣 : Ideal (𝓞 F)) (b : Rst D N) : ℝ :=
  L2D_beta 𝔣 b.1.1 * (((Ideal.absNorm b.2.1.1 : ℕ) : ℝ) ^ (-(4 : ℝ)) *
    (1 * ((Ideal.absNorm b.2.2.2.1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))))

include E in
lemma norm_Gp_le (h𝔥 : 𝔥 * simplePart r.1.1 = r.1.1) (hfg : 𝔥 = 𝔣 * 𝔤) (hl : 0 < l)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ υ κ (y : ℝ), 0 < y → ‖D.H υ κ y‖ ≤ C * y⁻¹) (b : Rst D N) :
    ‖Gp g D eU r 𝔥 𝔣 l b‖ ≤
      (C * l * (Ideal.absNorm (simplePart r.1.1) : ℝ) ^ 2 * (Ideal.absNorm 𝔣 : ℝ) ^ 2) *
        wt g D 𝔣 b := by
  have h𝔟 : r.1.1 ≠ ⊥ := r.1.2.1
  have hhe : IsExterior 𝔪 𝔥 := C3M.isExterior_of_mul_left (h𝔥.symm ▸ r.1.2)
  have hfe : IsExterior 𝔪 𝔣 := C3M.isExterior_of_mul_left (hfg ▸ hhe)
  have hde : IsExterior 𝔪 (simplePart r.1.1) := C3M.isExterior_of_mul_right (h𝔥.symm ▸ r.1.2)
  obtain ⟨⟨a, ha⟩, ⟨n, hn⟩, s, ⟨c, hc⟩⟩ := b
  have qa := absNorm_pos_real ha
  have qn := absNorm_pos_real hn.1
  have qc := absNorm_pos_real hc.1.1
  have qd := absNorm_pos_real hde.1
  have qf := absNorm_pos_real hfe.1
  set y := l⁻¹ * Ideal.absNorm a * Ideal.absNorm c * (Ideal.absNorm n : ℝ) ^ 3 /
    ((Ideal.absNorm (simplePart r.1.1) : ℝ) ^ 2 * (Ideal.absNorm 𝔣 : ℝ) ^ 2) with hy
  have hy0 : 0 < y := by positivity
  have hom := norm_omg_le' E g D eU (𝔥 := 𝔥) (𝔣 := 𝔣) r.2 a n s
  have hrho := norm_rho_le E g D eU r.2 𝔥 𝔣 a n s (simplePart r.1.1)
  have hlam := norm_lam_le E g D eU r.2 𝔥 𝔣 a n s c
  have hres := L2D_norm_residueSymbol_le ι 𝔪 (simplePart r.1.1) (g.gen c)
  have hβ := L2D_beta_nonneg 𝔣 a
  unfold Gp wt
  simp only
  rw [norm_mul, norm_mul, norm_div, norm_mul, norm_div, norm_mul, norm_pow, Complex.norm_natCast,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hHk : ‖Hk g D eU r.2 𝔥 𝔣 a n s y‖ ≤ C * y⁻¹ := by unfold Hk; exact hC _ _ y hy0
  have hsq : Real.sqrt (Ideal.absNorm c) = (Ideal.absNorm c : ℝ) ^ (1 / 2 : ℝ) :=
    Real.sqrt_eq_rpow _
  have e4 : ((Ideal.absNorm n : ℕ) : ℝ) ^ (-(4 : ℝ)) = ((Ideal.absNorm n : ℝ) ^ 4)⁻¹ := by
    rw [Real.rpow_neg qn.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have e32 : ((Ideal.absNorm c : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) =
      ((Ideal.absNorm c : ℝ) * Real.sqrt (Ideal.absNorm c))⁻¹ := by
    rw [Real.rpow_neg qc.le, hsq, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add qc, Real.rpow_one]
  rw [e4, e32]
  have hsqc := Real.sqrt_pos.2 qc
  have ha1 : (1 : ℝ) ≤ Ideal.absNorm a := L2D_one_le_absNorm ha
  calc ‖omg g D eU r.2 𝔥 𝔣 a n s‖ / (Ideal.absNorm n : ℝ) *
        ‖rho g D eU r.2 𝔥 𝔣 a n s (simplePart r.1.1)‖ *
        (‖lam g D eU r.2 𝔥 𝔣 a n s c‖ * ‖residueSymbol ι 𝔪 (simplePart r.1.1) (g.gen c)‖ ^ 3 /
          Real.sqrt (Ideal.absNorm c) * ‖Hk g D eU r.2 𝔥 𝔣 a n s y‖)
      ≤ L2D_beta 𝔣 a / (Ideal.absNorm n : ℝ) * 1 *
        (1 * 1 ^ 3 / Real.sqrt (Ideal.absNorm c) * (C * y⁻¹)) := by
        gcongr
    _ = (C * l * (Ideal.absNorm (simplePart r.1.1) : ℝ) ^ 2 * (Ideal.absNorm 𝔣 : ℝ) ^ 2) *
          (L2D_beta 𝔣 a * ((Ideal.absNorm n : ℝ) ^ 4)⁻¹ *
            ((Ideal.absNorm c : ℝ) * Real.sqrt (Ideal.absNorm c))⁻¹) *
          (Ideal.absNorm a : ℝ)⁻¹ := by
        rw [hy]; field_simp
    _ ≤ (C * l * (Ideal.absNorm (simplePart r.1.1) : ℝ) ^ 2 * (Ideal.absNorm 𝔣 : ℝ) ^ 2) *
          (L2D_beta 𝔣 a * ((Ideal.absNorm n : ℝ) ^ 4)⁻¹ *
            ((Ideal.absNorm c : ℝ) * Real.sqrt (Ideal.absNorm c))⁻¹) * 1 := by
        gcongr
        exact inv_le_one_of_one_le₀ ha1
    _ = _ := by ring

lemma summable_wt (h𝔣 : 𝔣 ≠ ⊥) : Summable (wt g D (N := N) 𝔣) := by
  have h1 : Summable fun a : {𝔞 : Ideal (𝓞 F) // 𝔞 ≠ ⊥} => L2D_beta 𝔣 a.1 := by
    apply summable_of_sum_le (c := L2D_E0 ^ L2D_omega 𝔣) (fun a => L2D_beta_nonneg _ _)
    intro s
    have := L2D_sum_beta_le 𝔣 h𝔣 (s.map (Function.Embedding.subtype _))
      (fun a ha => by
        rw [Finset.mem_map] at ha; obtain ⟨x, -, rfl⟩ := ha; exact x.2)
    rwa [Finset.sum_map] at this
  have h2 : Summable fun n : {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫} =>
      ((Ideal.absNorm n.1 : ℕ) : ℝ) ^ (-(4 : ℝ)) :=
    (T12B.summable_absNorm_rpow (F := F) (by norm_num)).comp_injective Subtype.val_injective
  have h3 : Summable fun c : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠} =>
      ((Ideal.absNorm c.1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) :=
    (T12B.summable_absNorm_rpow (F := F) (by norm_num)).comp_injective Subtype.val_injective
  have h4 : Summable fun _ : TT D N => (1 : ℝ) := summable_of_finite_support
    (Set.toFinite _)
  have n2 : 0 ≤ fun n : {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫} =>
      ((Ideal.absNorm n.1 : ℕ) : ℝ) ^ (-(4 : ℝ)) := fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have n3 : 0 ≤ fun c : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠} =>
      ((Ideal.absNorm c.1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have s34 := h4.mul_of_nonneg h3 (fun _ => zero_le_one) n3
  have s234 := h2.mul_of_nonneg s34 n2 (fun _ => mul_nonneg zero_le_one (n3 _))
  exact h1.mul_of_nonneg s234 (fun _ => L2D_beta_nonneg _ _)
    (fun _ => mul_nonneg (n2 _) (mul_nonneg zero_le_one (n3 _)))

include E in
lemma summable_Gp (h𝔥 : 𝔥 * simplePart r.1.1 = r.1.1) (hfg : 𝔥 = 𝔣 * 𝔤) (hl : 0 < l) :
    Summable (Gp g D eU r 𝔥 𝔣 l) := by
  obtain ⟨C, hC0, hC⟩ := H_le D
  have hhe : IsExterior 𝔪 𝔥 := C3M.isExterior_of_mul_left (h𝔥.symm ▸ r.1.2)
  have hfe : IsExterior 𝔪 𝔣 := C3M.isExterior_of_mul_left (hfg ▸ hhe)
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_Gp_le E g D eU r l h𝔥 hfg hl hC0 hC) ?_
  exact (summable_wt g D hfe.1).mul_left _

include E in
/-- Per active set: `∑'_x E_{prim 𝔣}(…) = ∑'_b Gp(𝔣, b)`. -/
lemma tsum_FA (h𝔥 : 𝔥 * simplePart r.1.1 = r.1.1) (hfg : 𝔥 = 𝔣 * 𝔤)
    (h𝔣 : Squarefree 𝔣 ∧ 𝔣 * 𝔣 ∣ 𝔥) (hl : 0 < l) :
    Summable (FA g D r 𝔥 𝔣 l) ∧ ∑' z, FA g D r 𝔥 𝔣 l z = ∑' b, Gp g D eU r 𝔥 𝔣 l b := by
  classical
  set V := {b : Rst D N // Valid g D r 𝔣 b}
  let ψ : V → RowClass 𝔪 := fun b => Psi g D eU 𝔤 b.1
  have hinj : Function.Injective ψ := fun b b' h =>
    Subtype.ext (Psi_inj g D eU r h𝔥 hfg h𝔣 b.2 b'.2 h)
  have hsupp : Function.support (FA g D r 𝔥 𝔣 l) ⊆ Set.range ψ := by
    intro z hz
    obtain ⟨b, hb, hbz⟩ := supp_sub E g D eU r l (𝔤 := 𝔤) h𝔥 hfg h𝔣 z hz
    exact ⟨⟨b, hb⟩, hbz⟩
  have hcomp : ∀ b : V, FA g D r 𝔥 𝔣 l (ψ b) = Gp g D eU r 𝔥 𝔣 l b.1 := fun b =>
    FA_Psi E g D eU r l h𝔥 hfg h𝔣 hl b.2
  have hGs : Function.support (Gp g D eU r 𝔥 𝔣 l) ⊆ {b | Valid g D r 𝔣 b} := by
    intro b hb
    by_contra hv
    exact hb (Gp_eq_zero E g D eU r l h𝔥 hfg h𝔣 hv)
  have hsum := summable_Gp E g D eU r l h𝔥 hfg hl
  refine ⟨?_, ?_⟩
  · rw [← hinj.summable_iff (fun x hx => by
      by_contra h; exact hx (hsupp h))]
    have : (FA g D r 𝔥 𝔣 l ∘ ψ) = fun b : V => Gp g D eU r 𝔥 𝔣 l b.1 := funext hcomp
    rw [this]
    exact hsum.subtype _
  · rw [← hinj.tsum_eq hsupp, ← tsum_subtype_eq_of_support_subset hGs]
    exact tsum_congr hcomp

end L3V

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3V_Sum2: the full regrouping — the cut's reflected sum is Cut63V's right side

`row_identity`: for a row `r`, `𝔥 𝔡 = 𝔟` and `l > 0`, the sum over the reflected frequencies of the
cut equals the key sum of Cut63V with `ω, ρ, λ, H` of `L3V_Keys`. The active sets `𝔣` are in
bijection with the subsets of `prim 𝔥` (`𝔥` is powerful).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-- The active sets. -/
abbrev KF (𝔥 : Ideal (𝓞 F)) : Type _ := {𝔣 : Ideal (𝓞 F) // Squarefree 𝔣 ∧ 𝔣 * 𝔣 ∣ 𝔥}

lemma finite_KF {𝔥 : Ideal (𝓞 F)} (h𝔥 : 𝔥 ≠ ⊥) : Finite (KF 𝔥) := by
  refine Finite.of_injective (fun 𝔣 : KF 𝔥 => (⟨𝔣.1, (L2D_mem_Fset h𝔥).2 𝔣.2⟩ : L2D_Fset 𝔥)) ?_
  intro a b h
  exact Subtype.ext (congrArg (fun x : L2D_Fset 𝔥 => x.1) h)

/-- `𝔣 ↦ prim 𝔣` is a bijection from the active sets onto the subsets of `prim 𝔥`. -/
lemma sum_KF {𝔟 𝔥 : Ideal (𝓞 F)} (h𝔟 : 𝔟 ≠ ⊥) (h𝔥 : 𝔥 * simplePart 𝔟 = 𝔟) [Fintype (KF 𝔥)]
    (φ : Finset (Ideal (𝓞 F)) → ℂ) :
    ∑ A ∈ (prim 𝔥).powerset, φ A = ∑ 𝔣 : KF 𝔥, φ (prim 𝔣.1) := by
  classical
  have hpow := L2D_powerful_of_mul 𝔟 𝔥 h𝔟 h𝔥
  have hh0 : 𝔥 ≠ ⊥ := hpow.1
  symm
  refine Finset.sum_bij (fun 𝔣 _ => prim 𝔣.1) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro 𝔣 _
    rw [Finset.mem_powerset]
    exact L2D_nf_subset_of_dvd hh0 ((dvd_mul_right _ _).trans 𝔣.2.2)
  · intro 𝔣 _ 𝔣' _ h
    have hf0 : 𝔣.1 ≠ ⊥ := fun h0 => hh0 (by
      have := 𝔣.2.2; rw [h0, Ideal.bot_mul] at this; exact zero_dvd_iff.1 this)
    have hf0' : 𝔣'.1 ≠ ⊥ := fun h0 => hh0 (by
      have := 𝔣'.2.2; rw [h0, Ideal.bot_mul] at this; exact zero_dvd_iff.1 this)
    apply Subtype.ext
    apply eq_of_cnt hf0 hf0'
    intro P _ _
    have h1 := (squarefree_iff_cnt hf0).1 𝔣.2.1 P
    have h2 := (squarefree_iff_cnt hf0').1 𝔣'.2.1 P
    have h3 : P ∈ prim 𝔣.1 ↔ P ∈ prim 𝔣'.1 := by
      rw [show prim 𝔣.1 = prim 𝔣'.1 from h]
    rw [mem_prim_iff, mem_prim_iff] at h3
    omega
  · intro A hA
    rw [Finset.mem_powerset] at hA
    have hApr : ∀ P ∈ A, P.IsPrime ∧ P ≠ ⊥ := fun P hP => prime_of_mem_prim (hA hP)
    set 𝔣 := ∏ P ∈ A, P ^ (1 : ℕ)
    have hc : ∀ P, cnt P 𝔣 = if P ∈ A then 1 else 0 := fun P =>
      cnt_prod_pow P A hApr (fun _ => 1)
    have hf0 : 𝔣 ≠ ⊥ := prod_pow_ne_bot A hApr _
    have hsq : Squarefree 𝔣 := by
      rw [squarefree_iff_cnt hf0]; intro P; rw [hc]; split_ifs <;> omega
    have hdvd : 𝔣 * 𝔣 ∣ 𝔥 := by
      rw [dvd_iff_normalizedFactors_le_normalizedFactors (mul_ne_zero hf0 hf0) hh0,
        Multiset.le_iff_count]
      intro P
      change cnt P (𝔣 * 𝔣) ≤ cnt P 𝔥
      rw [cnt_mul hf0 hf0, hc]
      split_ifs with hP
      · exact hpow.2 P (Multiset.mem_toFinset.1 (hA hP))
      · omega
    refine ⟨⟨𝔣, hsq, hdvd⟩, Finset.mem_univ _, ?_⟩
    ext P
    show P ∈ prim 𝔣 ↔ P ∈ A
    rw [mem_prim_iff, hc]
    by_cases hP : P ∈ A <;> simp [hP]

variable (E : Env ι 𝔪) (g : AllowedGen ι 𝔪) {χ : HeckeChar F 𝔪} (D : Data χ g) {N : ℕ}
  (eU : Fin N ≃ SClass 𝔪) (r : RowClass 𝔪) {𝔥 : Ideal (𝓞 F)} (l : ℝ)

/-- A cofactor `𝔤` with `𝔥 = 𝔣 𝔤`. -/
lemma exists_cofactor (𝔣 : KF 𝔥) : ∃ 𝔤, 𝔥 = 𝔣.1 * 𝔤 := (dvd_mul_right _ _).trans 𝔣.2.2

include E in
theorem row_identity (h𝔥 : 𝔥 * simplePart r.1.1 = r.1.1) (hl : 0 < l) :
    ∑' z : RowClass 𝔪, Eprod g r z * (D.L r.2 (nu g r z))⁻¹ *
        D.H r.2 (D.cls (nu g r z))
          ((Ideal.absNorm z.1.1 : ℝ) / ((Ideal.absNorm r.1.1 : ℝ) ^ 2 * l)) =
      ∑' k : KF 𝔥 × {𝔞 : Ideal (𝓞 F) // 𝔞 ≠ ⊥} × {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫} × TT D N,
        omg g D eU r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 / (Ideal.absNorm k.2.2.1.1 : ℂ) *
          rho g D eU r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (simplePart r.1.1) *
          ∑' 𝔠 : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠},
            lam g D eU r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 𝔠.1 *
              residueSymbol ι 𝔪 (simplePart r.1.1) (g.gen 𝔠.1) ^ 3 /
              ((Real.sqrt (Ideal.absNorm 𝔠.1) : ℝ) : ℂ) *
              Hk g D eU r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2
                (l⁻¹ * Ideal.absNorm k.2.1.1 * Ideal.absNorm 𝔠.1 *
                    (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3 /
                  ((Ideal.absNorm (simplePart r.1.1) : ℝ) ^ 2 *
                    (Ideal.absNorm k.1.1 : ℝ) ^ 2)) := by
  classical
  have h𝔟 : r.1.1 ≠ ⊥ := r.1.2.1
  have hh0 : 𝔥 ≠ ⊥ := (L2D_powerful_of_mul r.1.1 𝔥 h𝔟 h𝔥).1
  haveI := finite_KF hh0
  letI : Fintype (KF 𝔥) := Fintype.ofFinite _
  -- cofactors
  choose 𝔤 h𝔤 using fun 𝔣 : KF 𝔥 => exists_cofactor (𝔥 := 𝔥) 𝔣
  -- the left side, expanded over active sets
  have hL : ∀ z : RowClass 𝔪, Eprod g r z * (D.L r.2 (nu g r z))⁻¹ *
      D.H r.2 (D.cls (nu g r z)) ((Ideal.absNorm z.1.1 : ℝ) / ((Ideal.absNorm r.1.1 : ℝ) ^ 2 * l)) =
      ∑ 𝔣 : KF 𝔥, FA g D r 𝔥 𝔣.1 l z := by
    intro z
    rw [Eprod_expand E g r h𝔥 z, sum_KF h𝔟 h𝔥, Finset.sum_mul, Finset.sum_mul]
    rfl
  have hFA := fun 𝔣 : KF 𝔥 => tsum_FA E g D eU r l (𝔤 := 𝔤 𝔣) h𝔥 (h𝔤 𝔣) 𝔣.2 hl
  rw [tsum_congr hL, Summable.tsum_finsetSum (fun 𝔣 _ => (hFA 𝔣).1)]
  simp_rw [fun 𝔣 : KF 𝔥 => (hFA 𝔣).2]
  -- the right side, regrouped
  set G2 : KF 𝔥 × Rst D N → ℂ := fun p => Gp g D eU r 𝔥 p.1.1 l p.2 with hG2
  have hGs : ∀ 𝔣 : KF 𝔥, Summable (Gp g D eU r 𝔥 𝔣.1 l) := fun 𝔣 =>
    summable_Gp E g D eU r l (𝔤 := 𝔤 𝔣) h𝔥 (h𝔤 𝔣) hl
  have hG2s : Summable G2 := by
    have : G2 = fun p => ∑ 𝔣₀ : KF 𝔥, if p.1 = 𝔣₀ then Gp g D eU r 𝔥 𝔣₀.1 l p.2 else 0 := by
      funext p
      rw [Finset.sum_ite_eq]; simp [hG2]
    rw [this]
    refine summable_sum fun 𝔣₀ _ => ?_
    have hinj : Function.Injective (fun b : Rst D N => (𝔣₀, b)) := fun b b' h =>
      congrArg Prod.snd h
    rw [← hinj.summable_iff]
    · have : (fun p : KF 𝔥 × Rst D N => if p.1 = 𝔣₀ then Gp g D eU r 𝔥 𝔣₀.1 l p.2 else 0) ∘
          (fun b : Rst D N => (𝔣₀, b)) = Gp g D eU r 𝔥 𝔣₀.1 l := by
        funext b; simp
      rw [this]; exact hGs 𝔣₀
    · intro p hp
      rw [if_neg]
      rintro rfl
      exact hp ⟨p.2, rfl⟩
  -- reassociate the index `((𝔣, 𝔞, 𝔫, s), 𝔠) ↦ (𝔣, (𝔞, 𝔫, s, 𝔠))`
  let e : (KF 𝔥 × {𝔞 : Ideal (𝓞 F) // 𝔞 ≠ ⊥} × {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫} × TT D N) ×
      {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠} ≃ KF 𝔥 × Rst D N :=
    { toFun := fun q => (q.1.1, (q.1.2.1, q.1.2.2.1, q.1.2.2.2, q.2))
      invFun := fun p => ((p.1, p.2.1, p.2.2.1, p.2.2.2.1), p.2.2.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hinner : ∀ k : KF 𝔥 × {𝔞 : Ideal (𝓞 F) // 𝔞 ≠ ⊥} × {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫} ×
      TT D N,
      omg g D eU r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 / (Ideal.absNorm k.2.2.1.1 : ℂ) *
          rho g D eU r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (simplePart r.1.1) *
          ∑' 𝔠 : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠},
            lam g D eU r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 𝔠.1 *
              residueSymbol ι 𝔪 (simplePart r.1.1) (g.gen 𝔠.1) ^ 3 /
              ((Real.sqrt (Ideal.absNorm 𝔠.1) : ℝ) : ℂ) *
              Hk g D eU r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2
                (l⁻¹ * Ideal.absNorm k.2.1.1 * Ideal.absNorm 𝔠.1 *
                    (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3 /
                  ((Ideal.absNorm (simplePart r.1.1) : ℝ) ^ 2 *
                    (Ideal.absNorm k.1.1 : ℝ) ^ 2)) =
        ∑' 𝔠 : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠}, G2 (e (k, 𝔠)) := by
    intro k
    rw [← tsum_mul_left]
    rfl
  rw [tsum_congr hinner]
  have hG2e : Summable (G2 ∘ e) := (e.summable_iff).2 hG2s
  have hprod := Summable.tsum_prod' hG2e (fun k => hG2e.comp_injective (fun c c' h => by
      have := congrArg Prod.snd h; exact this))
  simp only [Function.comp_apply] at hprod
  rw [← hprod, e.tsum_eq (f := G2), Summable.tsum_prod' hG2s (fun 𝔣 => hGs 𝔣), tsum_fintype]

end L3V

end ArtinPrimitiveRoots

end
end

section
section
namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

/-! L3T: the candidate cut `L3T_Cut63V` — Lemma 6.3 *before* the exact radial smoothing.

It is Prop 5.1 + Cor 5.2 + Lemmas 5.3, 5.4 (sheet profiles), 6.1 (first formula, (6.?)
`eq:reflection-unreflected`), 6.2 and the unfolding in the proof of Lemma 6.3, for the quotient
average `T_m(l)` of (6.?) `eq:reflection-theta-average`:
* the forward side is `T_m(l) = ∑ γ₂(𝔠) q_𝔠^{-1/2} q_𝔫^{-1} ϑ(𝔄) χ_𝔄(m) V(q_𝔄 l)`, with the
  radial profile `V` of (5.20), whose Mellin transform is (5.21);
* the reflected side is (6.22)'s expansion with the unsmoothed sheet profiles
  `H(x/l)` (`H_{υ,κ}` of (6.?) `eq:reflection-profiles`, summed over `ℓ`) in place of
  `Φ(Z x)`; `H` obeys (5.17).
Cut63 follows from it by Lemma 5.5 (proved in `L3T_Gamma`/`L3T_Kernel`/`L3T_Smooth`) and the
`T`-average `B_m(Z) = ∫ K(T) T_m(T/Z) dT/T` (`L3T_Main`). -/

open Classical in
/-- The candidate cut: Lemma 6.3 before the exact radial smoothing (see the module doc). -/
def L3T_Cut63V (n : ℕ) (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) : Prop :=
  let βp : ℝ → ℕ → ℝ := fun q e =>
    if e = 0 then 1
    else if e % 3 = 1 then q ^ (-((e / 3 : ℕ) : ℝ))
    else if e % 3 = 0 then q ^ ((1 : ℝ) / 2 - ((e / 3 : ℕ) : ℝ))
    else 0
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪),
    ∃ (V : ℝ → ℝ) (rr : ℕ) (C₀ A₀ : ℝ), Measurable V ∧ 0 < C₀ ∧ 0 < A₀ ∧
      (∀ s : ℂ, -(5 / 6 : ℝ) < s.re →
        MellinConvergent (fun t => (V t : ℂ)) s ∧
        mellin (fun t => (V t : ℂ)) s =
          (C₀ : ℂ) * (A₀ : ℂ) ^ s * (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ rr) ∧
    ∃ (T : Type) (_ : Fintype T)
      (ω : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T → ℂ)
      (ρ : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T →
        Ideal (𝓞 F) → ℂ)
      (lam : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T →
        Ideal (𝓞 F) → ℂ)
      (H : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T → ℝ → ℂ)
      (α : ℝ), 0 < α ∧
      (∀ υ 𝔥 𝔣 𝔞 𝔫 s, ‖ω υ 𝔥 𝔣 𝔞 𝔫 s‖ ≤
        ∏ P ∈ (normalizedFactors 𝔣).toFinset,
          βp (Ideal.absNorm P) ((normalizedFactors 𝔞).count P)) ∧
      (∀ υ 𝔥 𝔣 𝔞 𝔫 s, (∃ P ∈ normalizedFactors 𝔞, ¬ P ∣ 𝔣) → ω υ 𝔥 𝔣 𝔞 𝔫 s = 0) ∧
      (∀ υ 𝔥 𝔣 𝔞 𝔫 s 𝔡, ‖ρ υ 𝔥 𝔣 𝔞 𝔫 s 𝔡‖ ≤ 1) ∧
      (∀ υ 𝔥 𝔣 𝔞 𝔫 s 𝔠, ‖lam υ 𝔥 𝔣 𝔞 𝔫 s 𝔠‖ ≤ 1) ∧
      (∀ υ 𝔥 𝔣 𝔞 𝔫 s, ContDiff ℝ 2 (fun t => H υ 𝔥 𝔣 𝔞 𝔫 s (Real.exp t))) ∧
      (∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ υ 𝔥 𝔣 𝔞 𝔫 s, ∀ j : ℕ, j ≤ 2 → ∀ t : ℝ,
        ‖iteratedDeriv j (fun t => H υ 𝔥 𝔣 𝔞 𝔫 s (Real.exp t)) t‖ ≤
          C * min (Real.exp (α * t)) (Real.exp (-(N * t)))) ∧
      (∀ (r : RowClass 𝔪) (𝔥 : Ideal (𝓞 F)), 𝔥 * simplePart r.1.1 = r.1.1 →
        ∀ l : ℝ, 0 < l →
        ∑' p : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠} ×
            {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫},
          gaussPhase g 2 p.1.1 /
              ((Real.sqrt (Ideal.absNorm p.1.1) * Ideal.absNorm p.2.1 : ℝ) : ℂ) *
            χ.thetaChar g (p.1.1 * p.2.1 ^ 3) *
            residueSymbol ι 𝔪 (p.1.1 * p.2.1 ^ 3) (rowElt g r) *
            ((V (Ideal.absNorm (p.1.1 * p.2.1 ^ 3) * l) : ℝ) : ℂ) =
          ∑' k : {𝔣 : Ideal (𝓞 F) // Squarefree 𝔣 ∧ 𝔣 * 𝔣 ∣ 𝔥} × {𝔞 : Ideal (𝓞 F) // 𝔞 ≠ ⊥} ×
              {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫} × T,
            ω r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 / (Ideal.absNorm k.2.2.1.1 : ℂ) *
              ρ r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (simplePart r.1.1) *
              ∑' 𝔠 : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠},
                lam r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 𝔠.1 *
                  residueSymbol ι 𝔪 (simplePart r.1.1) (g.gen 𝔠.1) ^ 3 /
                  ((Real.sqrt (Ideal.absNorm 𝔠.1) : ℝ) : ℂ) *
                  H r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2
                    (l⁻¹ * Ideal.absNorm k.2.1.1 * Ideal.absNorm 𝔠.1 *
                        (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3 /
                      ((Ideal.absNorm (simplePart r.1.1) : ℝ) ^ 2 *
                        (Ideal.absNorm k.1.1 : ℝ) ^ 2)))

end ArtinPrimitiveRoots

end
end

section
section
namespace ArtinPrimitiveRoots

open NumberField

/-! L2D: `U_S / U_S^6` is finite (library 4956b3f7, the S-unit count). -/

variable {F : Type*} [Field F] [NumberField F]

lemma L2D_placesOf_finite (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) : (placesOf 𝔪).Finite := by
  apply (Ideal.finite_factors h𝔪).subset
  intro v hv
  exact Ideal.dvd_iff_le.2 hv

lemma L2D_SClass_finite (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) [IsCyclotomicExtension {n} ℚ F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) : Finite (SClass 𝔪) := by
  have : NeZero n := ⟨hn0.ne'⟩
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ F
  have h6 : 6 ∣ n := Nat.dvd_trans (by norm_num) hn
  have hζ6 : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F ^ (n / 6)) 6 :=
    hζ.pow hn0 (Nat.div_mul_cancel h6).symm
  have hμ : (primitiveRoots 6 F).Nonempty :=
    ⟨_, (mem_primitiveRoots (by norm_num)).2 hζ6⟩
  have : Finite (placesOf 𝔪) := (L2D_placesOf_finite 𝔪 h𝔪).to_subtype
  have hc := NumberField.natCard_sUnit_quotient_range_powMonoidHom F (placesOf 𝔪) hμ
  apply Nat.finite_of_card_ne_zero
  change Nat.card (↥((placesOf 𝔪).unit F) ⧸
    (powMonoidHom 6 : ↥((placesOf 𝔪).unit F) →* ↥((placesOf 𝔪).unit F)).range) ≠ 0
  rw [hc]
  positivity

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3V_Main: Cut63V from the integrated cubic-theta functional equation `L3V_CutKP`

`L3V_cut63V_of_cut`: `L3V_CutKP n F ι → L3V_LocPkg n F ι → L3T_Cut63V n F ι` (the statement of
`exists_cutoff_exists_mellin_thetaAverage_eq_tsum`). Everything between the theta identity and
Cut63V is proved: Lemma 6.2's digit sums (6.13)–(6.15), the frequency parametrization (6.21), the
factor separation (6.27)–(6.29) with reciprocity, the coefficient bounds and the regrouping.
-/

set_option linter.style.haveILetI false

open NumberField UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

open L3V

theorem L3V_cut63V_of_cut (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ)
    (hcut : L3V_CutKP n F ι) (hloc : L3V_LocPkg n F ι) : L3T_Cut63V n F ι := by
  unfold L3T_Cut63V
  intro βp
  obtain ⟨N₁, hN₁⟩ := data_of_cut n F ι hcut
  obtain ⟨N₂, hN₂⟩ := env_of_locPkg n F ι hloc
  refine ⟨max N₁ N₂, fun 𝔪 h𝔪 hs χ g => ?_⟩
  have hmono : ∀ {M : ℕ}, M ≤ max N₁ N₂ → SmallPrimesDvd M 𝔪 :=
    fun hM P hP hP0 hle => hs P hP hP0 (hle.trans hM)
  obtain ⟨D, rr, C₀, A₀, hVm, hC₀, hA₀, hM⟩ :=
    hN₁ 𝔪 h𝔪 (hmono (le_max_left _ _)) χ g
  have E : Env ι 𝔪 := hN₂ 𝔪 h𝔪 (hmono (le_max_right _ _))
  haveI := L2D_SClass_finite n hn0 hn 𝔪 h𝔪
  set eU : Fin (Nat.card (SClass 𝔪)) ≃ SClass 𝔪 := (Finite.equivFin (SClass 𝔪)).symm
  refine ⟨D.V, rr, C₀, A₀, hVm, hC₀, hA₀, hM, TT D (Nat.card (SClass 𝔪)), inferInstance,
    omg g D eU, rho g D eU, lam g D eU, Hk g D eU, D.α, D.hα,
    fun υ 𝔥 𝔣 𝔞 𝔫 s => norm_omg_le E g D eU υ 𝔥 𝔣 𝔞 𝔫 s,
    fun υ 𝔥 𝔣 𝔞 𝔫 s h => omg_eq_zero g D eU υ 𝔥 𝔣 𝔞 𝔫 s h,
    fun υ 𝔥 𝔣 𝔞 𝔫 s 𝔡 => norm_rho_le E g D eU υ 𝔥 𝔣 𝔞 𝔫 s 𝔡,
    fun υ 𝔥 𝔣 𝔞 𝔫 s 𝔠 => norm_lam_le E g D eU υ 𝔥 𝔣 𝔞 𝔫 s 𝔠,
    fun υ 𝔥 𝔣 𝔞 𝔫 s => D.hH υ _, ?_, ?_⟩
  · intro N hN
    obtain ⟨C, hC⟩ := D.hHb N hN
    exact ⟨C, fun υ 𝔥 𝔣 𝔞 𝔫 s j hj t => hC υ _ j hj t⟩
  · intro r 𝔥 h𝔥 l hl
    have h1 := D.hid r l hl
    unfold fwd at h1
    rw [h1]
    exact row_identity E g D eU r l h𝔥 hl

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3V_Res: the residue map `O_P → R / P R` on `F`, and the local symbols

For a height-one prime `v ∉ S`:
* `L3V.res 𝔪 v w ∈ R / v R` for `v(w) ≤ 1` (`0` otherwise); `res_eq`: `res w = [y]` whenever
  `v(w − y) ≤ exp(−1)`; `res` is additive and multiplicative on `O_v`, `res y = [y]` on `R`,
  `res w = 0 ↔ v(w) < 1`.
* `localSymbol_eq`: `localSymbol ι 𝔪 P t = χ(res t)` (all `t`, `Good`);
* `localAddChar_eq`: `localAddChar g P w = ψ(−res w)` for `v(w) ≤ 1`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

open Classical in
/-- The residue of a `v`-integral element of `F` in `R / v R` (`0` if not `v`-integral). -/
noncomputable def res (𝔪 : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) (w : F) :
    SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
  if h : v.valuation F w ≤ 1 then
    Ideal.Quotient.mk _ (algebraMap (𝓞 F) (SInt 𝔪) (C3I.exists_val_sub_le (v := v) 1 w h).choose)
  else 0

lemma exp_neg_one_lt_one : (exp (-1 : ℤ) : ℤᵐ⁰) < 1 := by
  rw [← exp_zero]; exact exp_lt_exp.2 (by norm_num)

lemma mem_iff_val (hv : v ∉ placesOf 𝔪) (y : SInt 𝔪) :
    y ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) ↔ v.valuation F (y : F) ≤ exp (-1 : ℤ) := by
  have := C3I.mem_map_pow_iff (𝔪 := 𝔪) hv 1 y
  rw [pow_one] at this
  rw [this]; simp

lemma val_le_exp_iff_lt_one (x : F) : v.valuation F x ≤ exp (-1 : ℤ) ↔ v.valuation F x < 1 := by
  constructor
  · intro h; exact lt_of_le_of_lt h exp_neg_one_lt_one
  · intro h
    by_contra hc
    push Not at hc
    have := C3I.exp_le_of_lt (j := 0) (by simpa using hc)
    rw [exp_zero] at this
    exact absurd h (not_lt.2 this)

lemma mk_eq_of_approx (hv : v ∉ placesOf 𝔪) {w : F} {y : SInt 𝔪} {a : 𝓞 F}
    (h : v.valuation F (w - (y : F)) ≤ exp (-1 : ℤ))
    (ha : v.valuation F (w - algebraMap (𝓞 F) F a) ≤ exp (-((1 : ℕ) : ℤ))) :
    (Ideal.Quotient.mk (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
      (algebraMap (𝓞 F) (SInt 𝔪) a)) = Ideal.Quotient.mk _ y := by
  rw [Ideal.Quotient.eq, mem_iff_val hv]
  have h2 : ((algebraMap (𝓞 F) (SInt 𝔪) a - y : SInt 𝔪) : F) =
      -(w - algebraMap (𝓞 F) F a) + (w - (y : F)) := by
    rw [Subalgebra.coe_sub, C3I.coe_alg]; ring
  rw [h2]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ h)
  rw [Valuation.map_neg]
  simpa using ha

lemma res_eq (hv : v ∉ placesOf 𝔪) {w : F} {y : SInt 𝔪}
    (h : v.valuation F (w - (y : F)) ≤ exp (-1 : ℤ)) :
    res 𝔪 v w = Ideal.Quotient.mk _ y := by
  have hw : v.valuation F w ≤ 1 := by
    have h1 : w = (w - (y : F)) + (y : F) := by ring
    rw [h1]
    exact (Valuation.map_add _ _ _).trans
      (max_le (h.trans exp_neg_one_lt_one.le) (C3I.val_le_one hv y))
  rw [res, dif_pos hw]
  exact mk_eq_of_approx hv h (C3I.exists_val_sub_le (v := v) 1 w hw).choose_spec

lemma res_of_SInt (hv : v ∉ placesOf 𝔪) (y : SInt 𝔪) :
    res 𝔪 v (y : F) = Ideal.Quotient.mk _ y :=
  res_eq hv (by simp)

lemma exists_approx {w : F} (hw : v.valuation F w ≤ 1) :
    ∃ y : SInt 𝔪, v.valuation F (w - (y : F)) ≤ exp (-1 : ℤ) := by
  obtain ⟨a, ha⟩ := C3I.exists_val_sub_le (v := v) 1 w hw
  exact ⟨algebraMap (𝓞 F) (SInt 𝔪) a, by rw [C3I.coe_alg]; simpa using ha⟩

lemma res_of_not_le {w : F} (hw : ¬ v.valuation F w ≤ 1) : res 𝔪 v w = 0 := by
  rw [res, dif_neg hw]

lemma res_mul (hv : v ∉ placesOf 𝔪) {w w' : F} (hw : v.valuation F w ≤ 1)
    (hw' : v.valuation F w' ≤ 1) : res 𝔪 v (w * w') = res 𝔪 v w * res 𝔪 v w' := by
  obtain ⟨y, hy⟩ := exists_approx (𝔪 := 𝔪) hw
  obtain ⟨y', hy'⟩ := exists_approx (𝔪 := 𝔪) hw'
  rw [res_eq hv hy, res_eq hv hy', ← map_mul]
  apply res_eq hv
  have : w * w' - ((y * y' : SInt 𝔪) : F) = w * (w' - y') + (w - y) * (y' : F) := by
    rw [Subalgebra.coe_mul]; ring
  rw [this]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
  · rw [map_mul]
    calc v.valuation F w * v.valuation F (w' - y') ≤ 1 * exp (-1 : ℤ) := mul_le_mul' hw hy'
      _ = _ := one_mul _
  · rw [map_mul]
    calc v.valuation F (w - y) * v.valuation F (y' : F) ≤ exp (-1 : ℤ) * 1 :=
          mul_le_mul' hy (C3I.val_le_one hv y')
      _ = _ := mul_one _

lemma res_one (hv : v ∉ placesOf 𝔪) : res 𝔪 v (1 : F) = 1 := by
  have := res_of_SInt (𝔪 := 𝔪) hv 1
  simpa using this

lemma res_eq_zero_iff (hv : v ∉ placesOf 𝔪) {w : F} (hw : v.valuation F w ≤ 1) :
    res 𝔪 v w = 0 ↔ v.valuation F w < 1 := by
  obtain ⟨y, hy⟩ := exists_approx (𝔪 := 𝔪) hw
  rw [res_eq hv hy, Ideal.Quotient.eq_zero_iff_mem, mem_iff_val hv, val_le_exp_iff_lt_one]
  rw [val_le_exp_iff_lt_one] at hy
  constructor
  · intro h
    have h2 : w = (y : F) + (w - y) := by ring
    rw [h2]; exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt h hy)
  · intro h
    have h1 : (y : F) = w - (w - y) := by ring
    rw [h1]; exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h hy)

lemma res_ne_zero_of_val_eq_one (hv : v ∉ placesOf 𝔪) {w : F} (hw : v.valuation F w = 1) :
    res 𝔪 v w ≠ 0 := by
  rw [Ne, res_eq_zero_iff hv hw.le, hw]; exact lt_irrefl _

/-! ### The local symbols -/

section good

variable (h : C3I.Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
include h

lemma val_of_not_mem {z : SInt 𝔪} (hz : z ∉ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    v.valuation F (z : F) = 1 := C3I.val_eq_one_of_not_mem h hz

include hω in
lemma localSymbol_eq (t : F) :
    localSymbol ι 𝔪 v.asIdeal t = C3I.chi ι h hω (res 𝔪 v t) := by
  haveI := C3I.isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  rw [localSymbol]
  split_ifs with hex
  · set yz := hex.choose
    have hyz := hex.choose_spec
    have hz1 := val_of_not_mem h hyz.1
    have ht : v.valuation F t ≤ 1 := by
      have := congrArg (v.valuation F) hyz.2
      rw [map_mul, hz1, one_mul] at this
      rw [this]; exact C3I.val_le_one h.notS _
    have hres : res 𝔪 v (yz.1 : F) = res 𝔪 v (yz.2 : F) * res 𝔪 v t := by
      rw [← hyz.2, res_mul h.notS (C3I.val_le_one h.notS _) ht]
    rw [res_of_SInt h.notS, res_of_SInt h.notS] at hres
    rw [← C3I.chi_mk h hω, ← C3I.chi_mk h hω, hres, map_mul]
    have hz0 : Ideal.Quotient.mk (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) yz.2 ≠ 0 := by
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hyz.1
    have hu : IsUnit (Ideal.Quotient.mk (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) yz.2) :=
      Ne.isUnit hz0
    have hn : ‖C3I.chi ι h hω (Ideal.Quotient.mk _ yz.2)‖ = 1 := by
      have h6 := C3I.chi_pow_six_apply (ι := ι) h hω hz0
      have := norm_pow (C3I.chi ι h hω (Ideal.Quotient.mk _ yz.2)) 6
      rw [h6, norm_one] at this
      exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 this.symm)
    rw [mul_comm (C3I.chi ι h hω _), mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
    simp
  · -- no representation: `t` is not `v`-integral, or ...
    by_cases ht : v.valuation F t ≤ 1
    · exfalso
      apply hex
      obtain ⟨n, ⟨d, hd⟩, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer (K := F) t ht
      refine ⟨(algebraMap (𝓞 F) (SInt 𝔪) n, algebraMap (𝓞 F) (SInt 𝔪) d), ?_, ?_⟩
      · rw [show (algebraMap (𝓞 F) (SInt 𝔪) d) ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) ↔
            d ∈ v.asIdeal ^ 1 from by
              rw [← C3I.alg_mem_map_pow_iff h.notS 1 d, pow_one]]
        rw [pow_one]; exact hd
      · simp only [C3I.coe_alg]
        rw [mul_comm]; exact hnd
    · rw [res_of_not_le ht, MulChar.map_zero]

lemma val_sub_le_of_rep {w : F} {y z r : SInt 𝔪}
    (hz : z ∉ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hr : r ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) (he : (z : F) * (w - y) = r) :
    v.valuation F (w - y) ≤ exp (-1 : ℤ) := by
  have := congrArg (v.valuation F) he
  rw [map_mul, val_of_not_mem h hz, one_mul] at this
  rw [this]; exact (mem_iff_val h.notS r).1 hr

lemma localAddChar_eq (g : AllowedGen ι 𝔪) {w : F} (hw : v.valuation F w ≤ 1) :
    localAddChar g v.asIdeal w = C3I.psi g h (-(res 𝔪 v w)) := by
  rw [localAddChar]
  split_ifs with hex
  · set yzr := hex.choose
    have hyzr := hex.choose_spec
    have hres := res_eq h.notS (val_sub_le_of_rep h hyzr.1 hyzr.2.1 hyzr.2.2)
    rw [hres, ← map_neg, C3I.psi_mk, Subalgebra.coe_neg, neg_div]
  · exfalso
    apply hex
    obtain ⟨y, hy⟩ := exists_approx (𝔪 := 𝔪) hw
    have hy1 : v.valuation F (w - y) ≤ 1 := hy.trans exp_neg_one_lt_one.le
    obtain ⟨n, ⟨d, hd⟩, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer (K := F) (w - y) hy1
    have hdv : v.valuation F (algebraMap (𝓞 F) F d) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hd
    refine ⟨(y, algebraMap (𝓞 F) (SInt 𝔪) d, algebraMap (𝓞 F) (SInt 𝔪) n), ?_, ?_, ?_⟩
    · intro hm
      rw [mem_iff_val h.notS, C3I.coe_alg, hdv] at hm
      exact absurd hm (not_le.2 exp_neg_one_lt_one)
    · rw [mem_iff_val h.notS, C3I.coe_alg]
      have : algebraMap (𝓞 F) F n = (w - y) * algebraMap (𝓞 F) F d := hnd.symm
      rw [this, map_mul, hdv, mul_one]; exact hy
    · simp only [C3I.coe_alg]
      rw [mul_comm]; exact hnd

end good

end L3V

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3V_Loc: characters, Gauss sums and masks on `k_P = R / P R`

At a good prime `v` (with `χ = C3I.chi`, `ψ = C3I.psi`):
* `chi_ql`, `add_ql`: the cut's `χ_P(quotLift y)` and `e(−quotLift y / p)` are `χ y`, `ψ(−y)`;
* `conj_chi_pow`: `conj(χ y)^j = (χ^{5j}) y`; `tau_eq`: `τ_j = g(χ^{5j}, ψ)`;
* `norm_gs`, `norm_gs_le`: `‖g(χ^m, ψ)‖ = √q` (`6 ∤ m`), `≤ √q` (all `m`); `norm_tau`;
* the masks: `mask_zero_of_ne`, `norm_mask_zero_le`, `norm_mask_le`, `mask_mul`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

section loc

variable (h : C3I.Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (g : AllowedGen ι 𝔪)
include h hω

lemma chi_ql (y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    sexticResidueSymbol ι 𝔪 v.asIdeal (quotLift y) = C3I.chi ι h hω y := by
  rw [← C3I.chi_mk h hω, C3I.mk_quotLift]

omit hω in
lemma add_ql (y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    sAddChar 𝔪 (-((quotLift y : F) / (g.gen v.asIdeal : F))) = C3I.psi g h (-y) := by
  have := C3I.psi_mk g h (-(quotLift y))
  rw [map_neg, C3I.mk_quotLift] at this
  rw [this, Subalgebra.coe_neg, neg_div]

lemma chi_zero : C3I.chi ι h hω (0 : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) = 0 := by
  rw [C3I.chi_apply]; exact C3I.sexFun_zero

lemma norm_chi_eq_one {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) :
    ‖C3I.chi ι h hω y‖ = 1 := by
  have h6 := C3I.chi_pow_six_apply (ι := ι) h hω hy
  have := norm_pow (C3I.chi ι h hω y) 6
  rw [h6, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 this.symm

lemma norm_chi_le (y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    ‖C3I.chi ι h hω y‖ ≤ 1 := by
  by_cases hy : y = 0
  · rw [hy, chi_zero h hω, norm_zero]; exact zero_le_one
  · exact (norm_chi_eq_one (ι := ι) h hω hy).le

lemma conj_chi {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) :
    starRingEnd ℂ (C3I.chi ι h hω y) = C3I.chi ι h hω y ^ 5 := by
  have h6 := C3I.chi_pow_six_apply (ι := ι) h hω hy
  have hn := norm_chi_eq_one (ι := ι) h hω hy
  have h0 : C3I.chi ι h hω y ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hn; exact zero_ne_one hn
  have hc : starRingEnd ℂ (C3I.chi ι h hω y) * C3I.chi ι h hω y = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
  apply mul_right_cancel₀ h0
  rw [hc, ← pow_succ, h6]

lemma conj_chi_pow {j : ℕ} (hj : j ≠ 0) (y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    starRingEnd ℂ (C3I.chi ι h hω y) ^ j = (C3I.chi ι h hω ^ (5 * j)) y := by
  rw [MulChar.pow_apply' _ (by omega)]
  by_cases hy : y = 0
  · rw [hy, chi_zero h hω, map_zero, zero_pow hj, zero_pow (by omega)]
  · rw [conj_chi (ι := ι) h hω hy, ← pow_mul]

variable [Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))]

lemma tau_eq {j : ℕ} (hj : j ≠ 0) :
    tau g v.asIdeal j = gaussSum (C3I.chi ι h hω ^ (5 * j)) (C3I.psi g h) := by
  rw [← C3I.gs_inv_psi h hω g (5 * j)]
  unfold tau
  rw [finsum_eq_sum_of_fintype, gaussSum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [chi_ql h hω, add_ql h g, conj_chi_pow h hω hj, AddChar.inv_apply]

lemma norm_gs {m : ℕ} (hm : ¬ 6 ∣ m) :
    ‖gaussSum (C3I.chi ι h hω ^ m) (C3I.psi g h)‖ = Real.sqrt (Ideal.absNorm v.asIdeal) := by
  have h1 := C3I.gs_mul_gs h hω g (j := m) (k := 5 * m) hm (by omega)
  rw [← C3I.star_gs h hω g m (5 * m) (by omega), Complex.mul_conj, Complex.normSq_eq_norm_sq]
    at h1
  have h2 : ‖gaussSum (C3I.chi ι h hω ^ m) (C3I.psi g h)‖ ^ 2 = (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast h1
  rw [← h2, Real.sqrt_sq (norm_nonneg _)]

lemma one_le_absNorm : (1 : ℝ) ≤ Ideal.absNorm v.asIdeal := by
  have := C3I.absNorm_pos v
  exact_mod_cast this

lemma norm_gs_le (m : ℕ) :
    ‖gaussSum (C3I.chi ι h hω ^ m) (C3I.psi g h)‖ ≤ Real.sqrt (Ideal.absNorm v.asIdeal) := by
  by_cases hm : 6 ∣ m
  · obtain ⟨k, rfl⟩ := hm
    haveI := C3I.isMaximal_v h
    letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    have hone : C3I.chi ι h hω ^ (6 * k) = 1 := by
      rw [pow_mul, C3I.chi_pow_six h hω, one_pow]
    have hψ : C3I.psi g h ≠ 1 := by
      intro h1
      have hp := C3I.psi_isPrimitive g h
      have := hp (a := 1) one_ne_zero
      apply this
      rw [h1]; ext x; simp
    rw [hone, gaussSum_one_left hψ, norm_neg, norm_one]
    rw [Real.one_le_sqrt]
    exact one_le_absNorm h hω
  · exact (norm_gs h hω g hm).le

lemma norm_tau {j : ℕ} (hj : j ≠ 0) (hj6 : j < 6) :
    ‖tau g v.asIdeal j‖ = Real.sqrt (Ideal.absNorm v.asIdeal) := by
  rw [tau_eq h hω g hj, norm_gs h hω g (by omega)]

lemma sqrt_pos' : 0 < Real.sqrt (Ideal.absNorm v.asIdeal) :=
  Real.sqrt_pos.2 (by have := one_le_absNorm h hω; linarith)

/-! ### Masks -/

lemma mask_zero_of_ne {j : ℕ} (hj : j ≠ 0) : mask g v.asIdeal j 0 = 0 := by
  unfold mask
  rw [if_neg hj, chi_ql h hω, chi_zero h hω, map_zero, zero_pow hj, mul_zero]

omit hω in
lemma mask_zero_zero : mask g v.asIdeal 0 0 = 1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹ := by
  unfold mask; simp

lemma norm_mask_zero_le (j : ℕ) : ‖mask g v.asIdeal j 0‖ ≤ 1 := by
  by_cases hj : j = 0
  · subst hj
    rw [mask_zero_zero h g]
    have hq := one_le_absNorm h hω
    have : (1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹) = ((1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹ : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    have h1 : 0 < (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by positivity
    have h2 : (Ideal.absNorm v.asIdeal : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq
    constructor <;> linarith
  · rw [mask_zero_of_ne h hω g hj, norm_zero]; exact zero_le_one

lemma norm_mask_le {j : ℕ} (hj6 : j < 6) {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))}
    (hy : y ≠ 0) : ‖mask g v.asIdeal j y‖ ≤ (Real.sqrt (Ideal.absNorm v.asIdeal))⁻¹ := by
  have hq := one_le_absNorm h hω
  unfold mask
  by_cases hj : j = 0
  · rw [if_pos hj, if_neg hy, norm_neg, norm_inv, Complex.norm_natCast]
    apply inv_anti₀ (sqrt_pos' h hω)
    calc Real.sqrt (Ideal.absNorm v.asIdeal) ≤ Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = _ := Real.sqrt_sq (by linarith)
  · rw [if_neg hj, norm_mul, norm_inv, norm_tau h hω g hj hj6, norm_pow, chi_ql h hω,
      Complex.norm_conj]
    have := norm_chi_le (ι := ι) h hω y
    have h1 : ‖C3I.chi ι h hω y‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg _) this
    calc (Real.sqrt (Ideal.absNorm v.asIdeal))⁻¹ * ‖C3I.chi ι h hω y‖ ^ j
        ≤ (Real.sqrt (Ideal.absNorm v.asIdeal))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 (Real.sqrt_nonneg _))
      _ = _ := mul_one _

/-- `α(τ y) = conj(χ τ)^j α(y)` for `τ ≠ 0`. -/
lemma mask_mul {j : ℕ} {τ : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hτ : τ ≠ 0)
    (y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    mask g v.asIdeal j (τ * y) = starRingEnd ℂ (C3I.chi ι h hω τ) ^ j * mask g v.asIdeal j y := by
  haveI := C3I.isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  unfold mask
  by_cases hj : j = 0
  · subst hj
    have e : (τ * y = 0) ↔ (y = 0) := by simp [hτ]
    by_cases hy : y = 0
    · rw [if_pos rfl, if_pos rfl, if_pos (e.2 hy), if_pos hy, pow_zero, one_mul]
    · rw [if_pos rfl, if_pos rfl, if_neg (fun h' => hy (e.1 h')), if_neg hy, pow_zero, one_mul]
  · rw [if_neg hj, if_neg hj, chi_ql h hω, chi_ql h hω, map_mul, map_mul, mul_pow]
    ring

end loc

end L3V

end ArtinPrimitiveRoots

end
end

section
section
/-!
# L2A_FSQuot: exterior ideals of `𝓞 F` and of `R`

* `exists_pow_mul_mem`: every `r ∈ R` has `𝔪^N r ⊆ 𝓞`.
* `mem_of_map_mem`: `I R ∩ 𝓞 = I` for `I + 𝔪 = 1`.
* `exists_sub_mem_map`: `𝓞 → R / I R` is onto for `I + 𝔪 = 1`; `finite_quot_map`,
  `natCard_quot_map_le : #(R / I R) ≤ N I`.
-/

open NumberField IsDedekindDomain WithZero

namespace ArtinPrimitiveRoots.L2A

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- Every `r ∈ R` has `𝔪^N r ⊆ 𝓞` for some `N`. -/
lemma exists_pow_mul_mem (r : SInt 𝔪) : ∃ N : ℕ, ∀ w ∈ 𝔪 ^ N, ∃ c : 𝓞 F,
    algebraMap (𝓞 F) (SInt 𝔪) w * r = algebraMap (𝓞 F) (SInt 𝔪) c := by
  obtain ⟨b, d, hd, hbd⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (r : F)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  set N := Ideal.absNorm (Ideal.span {d}) with hN
  refine ⟨N, fun w hw => ?_⟩
  have hint : ∀ v : HeightOneSpectrum (𝓞 F),
      v.valuation F (algebraMap (𝓞 F) F w * (r : F)) ≤ 1 := by
    intro v
    by_cases hv : v ∈ placesOf 𝔪
    · have hvm : 𝔪 ≤ v.asIdeal := hv
      have hdN : d ∉ v.asIdeal ^ N := by
        intro hmem
        have hle : Ideal.span {d} ≤ v.asIdeal ^ N := (Ideal.span_singleton_le_iff_mem _).2 hmem
        have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
        rw [map_pow] at hdvd
        have hN0 : N ≠ 0 := by
          rw [hN, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hd0
        have h2 : 2 ≤ Ideal.absNorm v.asIdeal := by
          have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
            rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
          have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
            rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
          omega
        have := Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hdvd
        have h3 : 2 ^ N ≤ Ideal.absNorm v.asIdeal ^ N := Nat.pow_le_pow_left h2 N
        have h4 : N < 2 ^ N := Nat.lt_two_pow_self
        omega
      have hvd : exp (-(N : ℤ)) < v.valuation F (algebraMap (𝓞 F) F d) := by
        rw [C3I.val_alg, ← not_le, v.intValuation_le_pow_iff_mem]; exact hdN
      have hvw : v.valuation F (algebraMap (𝓞 F) F w) ≤ exp (-(N : ℤ)) := by
        rw [C3I.val_alg, v.intValuation_le_pow_iff_mem]
        exact Ideal.pow_right_mono hvm N hw
      have hdpos : v.valuation F (algebraMap (𝓞 F) F d) ≠ 0 := ne_zero_of_lt hvd
      have hxd : (r : F) * algebraMap (𝓞 F) F d = algebraMap (𝓞 F) F b := by
        rw [← hbd, div_mul_cancel₀]
        exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hd0
      have key : v.valuation F (algebraMap (𝓞 F) F w * (r : F)) *
          v.valuation F (algebraMap (𝓞 F) F d) ≤ 1 * v.valuation F (algebraMap (𝓞 F) F d) := by
        rw [← map_mul, show algebraMap (𝓞 F) F w * (r : F) * algebraMap (𝓞 F) F d =
          algebraMap (𝓞 F) F b * algebraMap (𝓞 F) F w by rw [mul_assoc, hxd]; ring, map_mul]
        exact mul_le_mul' (v.valuation_le_one b) (hvw.trans hvd.le)
      exact C3I.le_of_mul_le_mul_ne key hdpos
    · rw [map_mul]
      exact mul_le_one' (v.valuation_le_one w) (r.2 v hv)
  obtain ⟨c, hc⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F _ hint
  refine ⟨c, Subtype.ext ?_⟩
  rw [Subalgebra.coe_mul, C3I.coe_alg, C3I.coe_alg, hc]

/-- `I R ∩ 𝓞 = I` for an ideal `I` coprime to `𝔪`. -/
lemma mem_of_map_mem (I : Ideal (𝓞 F)) (hI : I ⊔ 𝔪 = ⊤) (a : 𝓞 F)
    (ha : algebraMap (𝓞 F) (SInt 𝔪) a ∈ I.map (algebraMap (𝓞 F) (SInt 𝔪))) : a ∈ I := by
  set φ := algebraMap (𝓞 F) (SInt 𝔪)
  have hinj : Function.Injective φ := by
    intro x y hxy
    have := congrArg (fun z : SInt 𝔪 => (z : F)) hxy
    simp only [φ, C3I.coe_alg] at this
    exact IsFractionRing.injective (𝓞 F) F this
  -- the predicate
  have hQ : ∀ x ∈ I.map φ, ∃ N : ℕ, ∀ w ∈ 𝔪 ^ N, ∃ i ∈ I, φ w * x = φ i := by
    intro x hx
    rw [Ideal.map] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i0, hi0, rfl⟩ := hx
      exact ⟨0, fun w _ => ⟨w * i0, I.mul_mem_left _ hi0, by rw [map_mul]⟩⟩
    | zero => exact ⟨0, fun w _ => ⟨0, I.zero_mem, by simp⟩⟩
    | add x y _ _ hx hy =>
      obtain ⟨N1, h1⟩ := hx
      obtain ⟨N2, h2⟩ := hy
      refine ⟨max N1 N2, fun w hw => ?_⟩
      obtain ⟨i1, hi1, e1⟩ := h1 w (Ideal.pow_le_pow_right (le_max_left _ _) hw)
      obtain ⟨i2, hi2, e2⟩ := h2 w (Ideal.pow_le_pow_right (le_max_right _ _) hw)
      exact ⟨i1 + i2, I.add_mem hi1 hi2, by rw [mul_add, e1, e2, map_add]⟩
    | smul r x _ hx =>
      obtain ⟨Nx, hNx⟩ := hx
      obtain ⟨Nr, hNr⟩ := exists_pow_mul_mem (𝔪 := 𝔪) r
      refine ⟨Nr + Nx, fun w hw => ?_⟩
      rw [pow_add] at hw
      refine Submodule.mul_induction_on hw ?_ ?_
      · intro w1 hw1 w2 hw2
        obtain ⟨c, hc⟩ := hNr w1 hw1
        obtain ⟨i, hi, ei⟩ := hNx w2 hw2
        refine ⟨c * i, I.mul_mem_left _ hi, ?_⟩
        rw [smul_eq_mul, map_mul, map_mul, ← hc, ← ei]; ring
      · rintro w1 w2 ⟨i1, hi1, e1⟩ ⟨i2, hi2, e2⟩
        exact ⟨i1 + i2, I.add_mem hi1 hi2, by rw [map_add, add_mul, e1, e2, map_add]⟩
  obtain ⟨N, hN⟩ := hQ _ ha
  have hcop : IsCoprime I (𝔪 ^ N) := (Ideal.isCoprime_iff_sup_eq.mpr hI).pow_right
  obtain ⟨u, hu, w, hw, huw⟩ := hcop.exists
  obtain ⟨i, hi, ei⟩ := hN w hw
  have : w * a = i := hinj (by rw [map_mul, ei])
  have ha' : a = u * a + w * a := by rw [← add_mul, huw, one_mul]
  rw [ha', this]
  exact I.add_mem (I.mul_mem_right _ hu) hi

end ArtinPrimitiveRoots.L2A

end
end

section
section
/-! # L3V_Val: valuations of allowed generators and the unit-part symbol `uSym`

* `val_gen_eq`: `v(gen I) = exp(−v_P(I))` for exterior `I` at a good prime;
* `vP P x = −log v(x)` (the `P`-adic valuation), `uSym g P x = χ_P(x p^{−v_P(x)})`, the symbol of the
  unit part;
* `uSym_mul`, `uSym_inv`, `uSym_pow_six`, `uSym_ne_zero`, `uSym_of_unit`, `uSym_SInt` (for
  `y ∈ R ∖ P R`: `uSym y = χ_P(y)`), `uSym_unit_pow_six` (`= 1` on `U_S^6`), `vP_gen`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

section good

variable (h : C3I.Good 𝔪 v) (g : AllowedGen ι 𝔪)
include h

lemma gen_not_mem_of_ne {Q : Ideal (𝓞 F)} (hQ : Q.IsPrime) (hQe : IsExterior 𝔪 Q)
    (hne : Q ≠ v.asIdeal) :
    g.gen Q ∉ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  intro hmem
  have hspan : Q.map (algebraMap (𝓞 F) (SInt 𝔪)) ≤ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← g.span_gen Q hQe, Ideal.span_le, Set.singleton_subset_iff]; exact hmem
  have hle : Q ≤ v.asIdeal := fun a ha =>
    L2A.mem_of_map_mem v.asIdeal h.cop a (hspan (Ideal.mem_map_of_mem _ ha))
  have hmax : Q.IsMaximal := hQ.isMaximal hQe.1
  exact hne (hmax.eq_of_le v.isPrime.ne_top hle)

lemma nf_prime {Q : Ideal (𝓞 F)} (hQ : Q.IsPrime) (hQ0 : Q ≠ ⊥) : normalizedFactors Q = {Q} := by
  rw [normalizedFactors_irreducible ((Ideal.prime_of_isPrime hQ0 hQ).irreducible), normalize_eq]

/-- `v(gen I) = exp(−v_P(I))`. -/
lemma val_gen_eq (I : Ideal (𝓞 F)) (hI : IsExterior 𝔪 I) :
    v.valuation F (g.gen I : F) = exp (-(((normalizedFactors I).count v.asIdeal : ℕ) : ℤ)) := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hI.1
  | h₂ u hu =>
    have hu' : u = ⊤ := Ideal.isUnit_iff.mp hu
    subst hu'
    obtain ⟨μ, hμ⟩ := C3B.isUnit_gen_top g
    rw [← hμ, C3I.val_unit h, C3B.normalizedFactors_top]
    simp
  | h₃ 𝔞 Q hane hQ ih =>
    have hQp : Q.IsPrime := Ideal.isPrime_of_prime hQ
    have hQe : IsExterior 𝔪 Q := C3M.isExterior_of_mul_left hI
    have hae : IsExterior 𝔪 𝔞 := C3M.isExterior_of_mul_right hI
    obtain ⟨ε, hε⟩ := C3M.gen_mul' g hQe hae
    rw [hε, Subalgebra.coe_mul, Subalgebra.coe_mul, Subalgebra.coe_pow, map_mul, map_mul, map_pow,
      C3I.val_unit h, one_pow, one_mul, ih hae, normalizedFactors_mul hQe.1 hae.1,
      nf_prime h hQp hQe.1, Multiset.count_add, Multiset.count_singleton]
    by_cases hQv : Q = v.asIdeal
    · subst hQv
      rw [C3I.val_pi g h, if_pos rfl, ← exp_add]
      congr 1; push_cast; ring
    · rw [C3I.val_eq_one_of_not_mem h (gen_not_mem_of_ne h g hQp hQe hQv), if_neg (Ne.symm hQv),
        one_mul, zero_add]

variable {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
include hω

end good

end L3V

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3V_Weyl: Lemma 6.2 — the digit sums of the local Weyl calculation

At a good prime `v`, for the cut's local data:
* `Wsph_eq`, `Wv` values and `norm_gaussPhase_two`;
* `Eloc_split`: for `k ≥ 1`, `E_P = α(0) W_P(a(ν)) + R_P`, `R_P = Rsum` the nonzero digits;
* `Wweyl_eq`: the per-digit value in terms of `χ(res t)`, `χ(v)`, `ψ`;
* (6.15) `Rsum_monomial`: `R(t) = R(1) χ(res t)^{b(j,e)}` for a `P`-unit `t`, with
  `b(j,0) = 8 + 5j ≡ 8 − j`, `b(j,e) = 4 + 2e` (`e > 0`);
* (6.14) `Rsum_one_vanish`: `j = 1`, `e > 0` gives `0`;
* `norm_Rsum_one_le`: `|R(1)| ≤ β_P(e)` of (6.20) (`L2D_betaP`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

section weyl

variable (h : C3I.Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (g : AllowedGen ι 𝔪)
variable [Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))]

include h hω

omit hω in
lemma Wv_mod0 {e : ℕ} (he : e % 3 = 0) :
    Wv g v.asIdeal e = (((Ideal.absNorm v.asIdeal : ℝ) ^ (-((e / 3 : ℕ) : ℝ)) : ℝ) : ℂ) := by
  unfold Wv; rw [if_pos he]

omit hω in
lemma Wv_mod1 {e : ℕ} (he : e % 3 = 1) :
    Wv g v.asIdeal e = (((Ideal.absNorm v.asIdeal : ℝ) ^ (-((e / 3 : ℕ) : ℝ) - 1 / 2) : ℝ) : ℂ) *
      gaussPhase g 2 v.asIdeal := by
  unfold Wv; rw [if_neg (by omega), if_pos he]

omit hω in
lemma Wv_mod2 {e : ℕ} (he : e % 3 = 2) : Wv g v.asIdeal e = 0 := by
  unfold Wv; rw [if_neg (by omega), if_neg (by omega)]

omit hω in
lemma Wv_zero : Wv g v.asIdeal 0 = 1 := by
  rw [Wv_mod0 h g (by norm_num)]; simp

lemma norm_gaussPhase_two : ‖gaussPhase g 2 v.asIdeal‖ = 1 := by
  rw [C3I.gaussPhase_eq h hω g (by norm_num : (2 : ℕ) ≠ 0), norm_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    norm_gs h hω g (by norm_num)]
  exact inv_mul_cancel₀ (sqrt_pos' h hω).ne'

open Classical in
lemma Eloc_split {k : ℕ} (hk : k ≠ 0) (e₀ : ℤ) (t : F) :
    Eloc g v.asIdeal k e₀ t =
      mask g v.asIdeal (k % 6) 0 * Wsph g v.asIdeal e₀ t + Rsum g v.asIdeal (k % 6) e₀ t := by
  unfold Eloc Rsum
  rw [if_neg hk, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  have : ∀ y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)),
      mask g v.asIdeal (k % 6) y *
          (if y = 0 then Wsph g v.asIdeal e₀ t else Wweyl g v.asIdeal e₀ t y) =
        (if y = 0 then mask g v.asIdeal (k % 6) 0 * Wsph g v.asIdeal e₀ t else 0) +
          mask g v.asIdeal (k % 6) y *
            (if y = 0 then 0 else Wweyl g v.asIdeal e₀ t y) := by
    intro y
    by_cases hy : y = 0
    · subst hy; simp
    · simp [hy]
  rw [Finset.sum_congr rfl (fun y _ => this y), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

lemma val_ql_eq_one {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) :
    v.valuation F (quotLift y : F) = 1 := by
  apply val_of_not_mem h
  rw [← Ideal.Quotient.eq_zero_iff_mem, C3I.mk_quotLift]; exact hy

lemma Wweyl_eq {t : F} (ht : v.valuation F t ≤ 1)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) {e₀ : ℤ}
    (he : 0 ≤ e₀ + 2) {x : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))}
    (hx : x * y = res 𝔪 v t) :
    Wweyl g v.asIdeal e₀ t y = Wv g v.asIdeal (e₀ + 2).toNat *
      C3I.chi ι h hω (res 𝔪 v t) ^ (4 + 2 * (e₀ + 2).toNat) * C3I.chi ι h hω y ^ 4 *
      (if (e₀ + 2).toNat = 0 then C3I.psi g h (-x) else 1) := by
  haveI := C3I.isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have hvq := val_ql_eq_one h hω hy
  have hq0 : (quotLift y : F) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hvq; exact zero_ne_one hvq
  set w := t / (quotLift y : F) with hw
  have hvw : v.valuation F w ≤ 1 := by
    rw [hw, map_div₀, hvq, div_one]; exact ht
  have hresw : res 𝔪 v w = x := by
    have h1 : res 𝔪 v (w * (quotLift y : F)) = res 𝔪 v w * y := by
      rw [res_mul h.notS hvw (C3I.val_le_one h.notS _), res_of_SInt h.notS, C3I.mk_quotLift]
    rw [hw, div_mul_cancel₀ _ hq0, ← hw, ← hx] at h1
    exact (mul_right_cancel₀ hy h1).symm
  have hvp : v.valuation F (g.gen v.asIdeal : F) ≤ 1 := C3I.val_le_one h.notS _
  have hresp : res 𝔪 v (g.gen v.asIdeal : F) = 0 := by
    rw [res_of_SInt h.notS, Ideal.Quotient.eq_zero_iff_mem]
    have := C3I.gen_mem g h 1
    rwa [pow_one] at this
  have key : ∀ n : ℕ, v.valuation F ((g.gen v.asIdeal : F) ^ n * w) ≤ 1 ∧
      res 𝔪 v ((g.gen v.asIdeal : F) ^ n * w) = if n = 0 then x else 0 := by
    intro n
    induction n with
    | zero => simp [hvw, hresw]
    | succ n ih =>
      have e1 : (g.gen v.asIdeal : F) ^ (n + 1) * w =
          (g.gen v.asIdeal : F) * ((g.gen v.asIdeal : F) ^ n * w) := by ring
      rw [e1, map_mul, res_mul h.notS hvp ih.1, hresp, zero_mul]
      refine ⟨?_, by simp⟩
      calc v.valuation F (g.gen v.asIdeal : F) * v.valuation F ((g.gen v.asIdeal : F) ^ n * w)
          ≤ 1 * 1 := mul_le_mul' hvp ih.1
        _ = 1 := one_mul 1
  have e2 : (g.gen v.asIdeal : F) ^ (e₀ + 2).toNat * t / (quotLift y : F) =
      (g.gen v.asIdeal : F) ^ (e₀ + 2).toNat * w := by rw [hw, mul_div_assoc]
  unfold Wweyl
  rw [if_neg (not_lt.2 he), localSymbol_eq h hω, chi_ql h hω, e2,
    localAddChar_eq h g (key _).1, (key _).2]
  split_ifs with hn
  · rfl
  · rw [neg_zero, AddChar.map_zero_eq_one]

open Classical in
/-- `R(t)` for `e > 0`: `W_e χ(res t)^{4+2e} ∑_{v ≠ 0} α(v) χ(v)^4`. -/
lemma Rsum_pos {j : ℕ} {e₀ : ℤ} (he : 0 < e₀ + 2) {t : F} (ht : v.valuation F t ≤ 1) :
    Rsum g v.asIdeal j e₀ t = Wv g v.asIdeal (e₀ + 2).toNat *
      C3I.chi ι h hω (res 𝔪 v t) ^ (4 + 2 * (e₀ + 2).toNat) *
      ∑ y, mask g v.asIdeal j y * (if y = 0 then 0 else C3I.chi ι h hω y ^ 4) := by
  haveI := C3I.isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  unfold Rsum
  rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : y = 0
  · simp [hy]
  · rw [if_neg hy, if_neg hy, Wweyl_eq h hω g ht hy he.le (x := res 𝔪 v t * y⁻¹)
      (by rw [mul_assoc, inv_mul_cancel₀ hy, mul_one]), if_neg (by omega)]
    ring

open Classical in
/-- `R(t)` for `e = 0`. -/
lemma Rsum_zero {j : ℕ} {e₀ : ℤ} (he : e₀ + 2 = 0) {t : F} (ht : v.valuation F t ≤ 1) :
    haveI := C3I.isMaximal_v h
    letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    Rsum g v.asIdeal j e₀ t = C3I.chi ι h hω (res 𝔪 v t) ^ 4 *
      ∑ y, mask g v.asIdeal j y *
        (if y = 0 then 0 else C3I.chi ι h hω y ^ 4 * C3I.psi g h (-(res 𝔪 v t * y⁻¹))) := by
  haveI := C3I.isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  unfold Rsum
  rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : y = 0
  · simp [hy]
  · rw [if_neg hy, if_neg hy, Wweyl_eq h hω g ht hy (by omega) (x := res 𝔪 v t * y⁻¹)
      (by rw [mul_assoc, inv_mul_cancel₀ hy, mul_one])]
    have e1 : (e₀ + 2).toNat = 0 := by omega
    rw [e1, if_pos rfl, Wv_zero h g]
    ring

lemma res_one' : res 𝔪 v (1 : F) = 1 := res_one h.notS

open Classical in
/-- (6.15): `R(t) = R(1) χ(res t)^{b(j,e)}` for a `P`-unit `t`. -/
lemma Rsum_monomial {j : ℕ} {e₀ : ℤ} (he : 0 ≤ e₀ + 2) {t : F} (ht : v.valuation F t = 1) :
    Rsum g v.asIdeal j e₀ t =
      Rsum g v.asIdeal j e₀ 1 * C3I.chi ι h hω (res 𝔪 v t) ^ bexp j (e₀ + 2).toNat := by
  haveI := C3I.isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have h1 : v.valuation F (1 : F) ≤ 1 := by rw [map_one]
  have hτ : res 𝔪 v t ≠ 0 := res_ne_zero_of_val_eq_one h.notS ht
  rcases he.lt_or_eq with hpos | hz
  · rw [Rsum_pos h hω g hpos ht.le, Rsum_pos h hω g hpos h1, res_one' h hω, map_one, one_pow,
      bexp, if_neg (by omega)]
    ring
  · have hz' : e₀ + 2 = 0 := hz.symm
    rw [Rsum_zero h hω g hz' ht.le, Rsum_zero h hω g hz' h1, res_one' h hω, map_one, one_pow,
      one_mul, bexp, if_pos (by omega)]
    set τ := res 𝔪 v t
    rw [← Fintype.sum_equiv (Equiv.mulLeft₀ τ hτ) (fun z => mask g v.asIdeal j (τ * z) *
        (if τ * z = 0 then 0 else C3I.chi ι h hω (τ * z) ^ 4 *
          C3I.psi g h (-(τ * (τ * z)⁻¹)))) _ (fun z => rfl)]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [mask_mul h hω g hτ, one_mul]
    by_cases hz0 : z = 0
    · simp [hz0]
    · have hτz : τ * z ≠ 0 := mul_ne_zero hτ hz0
      have e3 : τ * (τ * z)⁻¹ = z⁻¹ := by field_simp
      rw [if_neg hτz, if_neg hz0, e3, map_mul]
      have hc : starRingEnd ℂ (C3I.chi ι h hω τ) ^ j = C3I.chi ι h hω τ ^ (5 * j) := by
        rw [conj_chi (ι := ι) h hω hτ, ← pow_mul]
      rw [hc]
      ring

open Classical in
/-- (6.14): for `j = 1` the digit sum vanishes when `e > 0`. -/
lemma Rsum_one_vanish {e₀ : ℤ} (he : 0 < e₀ + 2) {t : F} (ht : v.valuation F t ≤ 1) :
    Rsum g v.asIdeal 1 e₀ t = 0 := by
  rw [Rsum_pos h hω g he ht]
  have hs : ∑ y, mask g v.asIdeal 1 y * (if y = 0 then 0 else C3I.chi ι h hω y ^ 4) = 0 := by
    have : ∀ y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)),
        mask g v.asIdeal 1 y * (if y = 0 then 0 else C3I.chi ι h hω y ^ 4) =
          (tau g v.asIdeal 1)⁻¹ * (C3I.chi ι h hω ^ 3) y := by
      intro y
      unfold mask
      rw [if_neg one_ne_zero, chi_ql h hω, pow_one, MulChar.pow_apply' _ (by norm_num)]
      by_cases hy : y = 0
      · simp [hy, chi_zero (ι := ι) h hω]
      · rw [if_neg hy, conj_chi (ι := ι) h hω hy, mul_assoc, ← pow_add,
          show 5 + 4 = 6 + 3 by norm_num, pow_add, C3I.chi_pow_six_apply h hω hy, one_mul]
    rw [Finset.sum_congr rfl (fun y _ => this y), ← Finset.mul_sum]
    haveI := C3I.isMaximal_v h
    letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    rw [MulChar.sum_eq_zero_of_ne_one (C3I.chi_pow_ne_one h hω (by norm_num)), mul_zero]
  rw [hs, mul_zero]

end weyl

end L3V

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3V_Bound: the local majorant `|s_{P,j,e}| ≤ β_P(e)` (Lemma 6.2 bounds, (6.20)) -/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

section bound

variable (h : C3I.Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (g : AllowedGen ι 𝔪)
variable [Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))]

include h hω

lemma chi_inv' {z : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hz : z ≠ 0) :
    haveI := C3I.isMaximal_v h
    letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    C3I.chi ι h hω z⁻¹ = starRingEnd ℂ (C3I.chi ι h hω z) := by
  haveI := C3I.isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have h1 : C3I.chi ι h hω z * C3I.chi ι h hω z⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hz, map_one]
  have hn := norm_chi_eq_one (ι := ι) h hω hz
  have h2 : C3I.chi ι h hω z * starRingEnd ℂ (C3I.chi ι h hω z) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
  have h0 : C3I.chi ι h hω z ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hn; exact zero_ne_one hn
  exact mul_left_cancel₀ h0 (h1.trans h2.symm)

lemma card_eq : (Fintype.card (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) : ℝ) =
    Ideal.absNorm v.asIdeal := by
  rw [C3I.card_L h hω]

lemma sq_div_sqrt : (Ideal.absNorm v.asIdeal : ℝ) * (Real.sqrt (Ideal.absNorm v.asIdeal))⁻¹ =
    Real.sqrt (Ideal.absNorm v.asIdeal) := by
  have hs := sqrt_pos' h hω
  have : (Ideal.absNorm v.asIdeal : ℝ) = Real.sqrt (Ideal.absNorm v.asIdeal) ^ 2 :=
    (Real.sq_sqrt (by positivity)).symm
  rw [this, Real.sqrt_sq hs.le]
  field_simp

open Classical in
lemma norm_sum_mask_le {j : ℕ} (hj : j < 6) (f : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) → ℂ)
    (hf : ∀ y, ‖f y‖ ≤ 1) :
    ‖∑ y, mask g v.asIdeal j y * (if y = 0 then 0 else f y)‖ ≤
      Real.sqrt (Ideal.absNorm v.asIdeal) := by
  refine (norm_sum_le _ _).trans ?_
  have hb : ∀ y ∈ (Finset.univ : Finset (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))),
      ‖mask g v.asIdeal j y * (if y = 0 then 0 else f y)‖ ≤
        (Real.sqrt (Ideal.absNorm v.asIdeal))⁻¹ := by
    intro y _
    by_cases hy : y = 0
    · simp [hy]
    · rw [if_neg hy, norm_mul]
      calc ‖mask g v.asIdeal j y‖ * ‖f y‖ ≤ (Real.sqrt (Ideal.absNorm v.asIdeal))⁻¹ * 1 :=
            mul_le_mul (norm_mask_le h hω g hj hy) (hf y) (norm_nonneg _)
              (inv_nonneg.2 (Real.sqrt_nonneg _))
        _ = _ := mul_one _
  refine (Finset.sum_le_sum hb).trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_eq h hω, sq_div_sqrt h hω]

lemma norm_Wv_mul_sqrt_le {e : ℕ} (he : e ≠ 0) :
    ‖Wv g v.asIdeal e‖ * Real.sqrt (Ideal.absNorm v.asIdeal) ≤
      L2D_betaP (Ideal.absNorm v.asIdeal) e := by
  have hq : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
    have := one_le_absNorm h hω; linarith
  have hsq : Real.sqrt (Ideal.absNorm v.asIdeal) = (Ideal.absNorm v.asIdeal : ℝ) ^ (1 / 2 : ℝ) :=
    Real.sqrt_eq_rpow _
  unfold L2D_betaP
  rw [if_neg he]
  rcases (by omega : e % 3 = 0 ∨ e % 3 = 1 ∨ e % 3 = 2) with h0 | h1 | h2
  · rw [if_neg (by omega), if_pos h0, Wv_mod0 h g h0, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hq.le _), hsq, ← Real.rpow_add hq]
    apply le_of_eq; congr 1; ring
  · rw [if_pos h1, Wv_mod1 h g h1, norm_mul, norm_gaussPhase_two h hω g, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hq.le _), hsq,
      ← Real.rpow_add hq]
    apply le_of_eq; congr 1; ring
  · rw [if_neg (by omega), if_neg (by omega), Wv_mod2 h g h2, norm_zero, zero_mul]

open Classical in
/-- `|R_{P,j,e}(1)| ≤ β_P(e)`. -/
lemma norm_Rsum_one_le {j : ℕ} (hj : j < 6) {e₀ : ℤ} (he : 0 ≤ e₀ + 2) :
    ‖Rsum g v.asIdeal j e₀ 1‖ ≤ L2D_betaP (Ideal.absNorm v.asIdeal) (e₀ + 2).toNat := by
  haveI := C3I.isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have h1 : v.valuation F (1 : F) ≤ 1 := by rw [map_one]
  rcases he.lt_or_eq with hpos | hz
  · rw [Rsum_pos h hω g hpos h1, res_one' h hω, map_one, one_pow, mul_one, norm_mul]
    have hs := norm_sum_mask_le h hω g hj (fun y => C3I.chi ι h hω y ^ 4)
      (fun y => by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_chi_le (ι := ι) h hω y))
    refine (mul_le_mul_of_nonneg_left hs (norm_nonneg _)).trans ?_
    exact norm_Wv_mul_sqrt_le h hω g (by omega)
  · have hz' : e₀ + 2 = 0 := hz.symm
    have e0 : (e₀ + 2).toNat = 0 := by omega
    rw [Rsum_zero h hω g hz' h1, res_one' h hω, map_one, one_pow, one_mul, e0]
    unfold L2D_betaP; rw [if_pos rfl]
    by_cases hj0 : j = 0
    · subst hj0
      refine (norm_sum_le _ _).trans ?_
      have hb : ∀ y ∈ (Finset.univ : Finset (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))),
          ‖mask g v.asIdeal 0 y * (if y = 0 then 0 else C3I.chi ι h hω y ^ 4 *
            C3I.psi g h (-(1 * y⁻¹)))‖ ≤ (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
        intro y _
        by_cases hy : y = 0
        · simp [hy]
        · rw [if_neg hy, norm_mul, norm_mul, norm_pow]
          unfold mask
          rw [if_pos rfl, if_neg hy, norm_neg, norm_inv, Complex.norm_natCast]
          have hc := pow_le_one₀ (n := 4) (norm_nonneg _) (norm_chi_le (ι := ι) h hω y)
          have hp : ‖C3I.psi g h (-(1 * y⁻¹))‖ = 1 := AddChar.norm_apply _ _
          rw [hp, mul_one]
          calc (Ideal.absNorm v.asIdeal : ℝ)⁻¹ * ‖C3I.chi ι h hω y‖ ^ 4
              ≤ (Ideal.absNorm v.asIdeal : ℝ)⁻¹ * 1 :=
                mul_le_mul_of_nonneg_left hc (by positivity)
            _ = _ := mul_one _
      refine (Finset.sum_le_sum hb).trans ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_eq h hω]
      have := one_le_absNorm h hω
      rw [mul_inv_cancel₀ (by linarith)]
    · -- substitute `y ↦ y⁻¹`: a Gauss sum of `χ^{j+20}`
      have hsum : ∑ y, mask g v.asIdeal j y * (if y = 0 then 0 else C3I.chi ι h hω y ^ 4 *
            C3I.psi g h (-(1 * y⁻¹))) =
          (tau g v.asIdeal j)⁻¹ * gaussSum (C3I.chi ι h hω ^ (j + 20)) (C3I.psi g h) := by
        rw [← C3I.gs_inv_psi h hω g (j + 20), gaussSum, Finset.mul_sum]
        rw [← Fintype.sum_equiv (Equiv.inv _) (fun z => mask g v.asIdeal j z⁻¹ *
          (if z⁻¹ = 0 then 0 else C3I.chi ι h hω z⁻¹ ^ 4 * C3I.psi g h (-(1 * z⁻¹⁻¹)))) _
          (fun z => rfl)]
        refine Finset.sum_congr rfl fun z _ => ?_
        unfold mask
        rw [if_neg hj0, chi_ql h hω, MulChar.pow_apply' _ (by omega), AddChar.inv_apply]
        by_cases hz : z = 0
        · simp [hz, chi_zero (ι := ι) h hω]
        · rw [if_neg (inv_ne_zero hz), inv_inv, one_mul, chi_inv' (ι := ι) h hω hz,
            Complex.conj_conj, conj_chi (ι := ι) h hω hz, ← pow_mul, pow_add]
          ring
      rw [hsum, norm_mul, norm_inv, norm_tau h hω g hj0 hj]
      calc (Real.sqrt (Ideal.absNorm v.asIdeal))⁻¹ *
            ‖gaussSum (C3I.chi ι h hω ^ (j + 20)) (C3I.psi g h)‖
          ≤ (Real.sqrt (Ideal.absNorm v.asIdeal))⁻¹ * Real.sqrt (Ideal.absNorm v.asIdeal) :=
            mul_le_mul_of_nonneg_left (norm_gs_le h hω g _) (inv_nonneg.2 (Real.sqrt_nonneg _))
        _ = 1 := inv_mul_cancel₀ (sqrt_pos' h hω).ne'

end bound

end L3V

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3I_Cut: the cutoff — exterior primes of `ℚ(μ_n)`, `12 ∣ n`, are good

`N₀ = max(3^[F:ℚ], N 𝔇)`: an exterior prime has norm `> N₀`, so it lies over neither `2` nor `3`
(`12 ∣ N P − 1`) and does not divide the different. -/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F]

/-- In `ℚ(μ_n)` with `12 ∣ n`, a prime of norm `> 3^[F:ℚ]` has `12 ∣ N P − 1`. -/
theorem twelve_dvd_absNorm_sub_one (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    [IsCyclotomicExtension {n} ℚ F] (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hQ : 3 ^ Module.finrank ℤ (𝓞 F) < Ideal.absNorm P) : 12 ∣ Ideal.absNorm P - 1 := by
  have : P.IsMaximal := hP.isMaximal hP0
  let _ := Ideal.Quotient.field P
  have : Finite (𝓞 F ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP0
  let _ : Fintype (𝓞 F ⧸ P) := Fintype.ofFinite _
  set Q := Ideal.absNorm P
  have hd : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
  have h23 : 2 ^ Module.finrank ℤ (𝓞 F) ≤ 3 ^ Module.finrank ℤ (𝓞 F) :=
    Nat.pow_le_pow_left (by norm_num) _
  have h2 : ¬ 2 ∣ Q := fun h => by
    have := C3B.absNorm_le_of_prime_dvd 2 Nat.prime_two P hP0 h; omega
  have h3 : ¬ 3 ∣ Q := fun h => by
    have := C3B.absNorm_le_of_prime_dvd 3 Nat.prime_three P hP0 h; omega
  have hcop : Q.Coprime 12 := by
    have c2 : Q.Coprime 2 :=
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2))
    have c3 : Q.Coprime 3 :=
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3))
    have : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
    rw [this]; exact Nat.Coprime.mul_right (Nat.Coprime.pow_right 2 c2) c3
  have : NeZero n := ⟨hn0.ne'⟩
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ F
  have hζ12 : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F ^ (n / 12)) 12 :=
    hζ.pow hn0 (Nat.div_mul_cancel hn).symm
  have hω : IsPrimitiveRoot hζ12.toInteger 12 := hζ12.toInteger_isPrimitiveRoot
  have hQ1 : Q ≠ 1 := by
    have : 3 ≤ 3 ^ Module.finrank ℤ (𝓞 F) := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hd
    omega
  have hωb : IsPrimitiveRoot (Ideal.Quotient.mk P hζ12.toInteger) 12 :=
    hω.idealQuotient_mk hQ1 hcop
  have h1 : Ideal.Quotient.mk P hζ12.toInteger ^ (Q - 1) = 1 := by
    rw [show Q = Fintype.card (𝓞 F ⧸ P) from (C3B.card_quot P hP0).symm]
    exact FiniteField.pow_card_sub_one_eq_one _ (hωb.ne_zero (by norm_num))
  exact (hωb.pow_eq_one_iff_dvd _).mp h1

/-- A primitive sixth root of unity in `𝓞 F`. -/
theorem exists_prim_six (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) [IsCyclotomicExtension {n} ℚ F] :
    ∃ ω : 𝓞 F, IsPrimitiveRoot ω 6 := by
  have : NeZero n := ⟨hn0.ne'⟩
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ F
  have h6 : 6 ∣ n := Nat.dvd_trans (by norm_num) hn
  have hζ6 : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F ^ (n / 6)) 6 :=
    hζ.pow hn0 (Nat.div_mul_cancel h6).symm
  exact ⟨hζ6.toInteger, hζ6.toInteger_isPrimitiveRoot⟩

/-- The cutoff. -/
noncomputable def cutN (F : Type*) [Field F] [NumberField F] : ℕ :=
  max (3 ^ Module.finrank ℤ (𝓞 F)) (Ideal.absNorm (differentIdeal ℤ (𝓞 F)))

/-- Exterior primes are good once `N₀ ≥ cutN F`. -/
theorem good_of_exterior (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) [IsCyclotomicExtension {n} ℚ F]
    {N₀ : ℕ} (hN₀ : cutN F ≤ N₀) {𝔪 : Ideal (𝓞 F)} (hsm : SmallPrimesDvd N₀ 𝔪)
    {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hext : IsExterior 𝔪 P) :
    Good 𝔪 (⟨P, hP, hext.1⟩ : HeightOneSpectrum (𝓞 F)) := by
  have hbig : N₀ < Ideal.absNorm P := by
    by_contra hcon
    apply hP.ne_top
    rw [eq_top_iff, ← hext.2]
    exact sup_le le_rfl (hsm P hP hext.1 (by omega))
  have h1 : 3 ^ Module.finrank ℤ (𝓞 F) ≤ cutN F := le_max_left _ _
  have h2 : Ideal.absNorm (differentIdeal ℤ (𝓞 F)) ≤ cutN F := le_max_right _ _
  refine ⟨hext.2, twelve_dvd_absNorm_sub_one n hn0 hn P hP hext.1 (by omega), ?_⟩
  intro hD
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hD
  have hD0 : Ideal.absNorm (differentIdeal ℤ (𝓞 F)) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact differentIdeal_ne_bot
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hD0) hdvd
  change Ideal.absNorm P ≤ _ at this
  omega

end C3I

open NumberField

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3M_Main: CutMul from `HypAdd` and `HypChi`

`b(P^{e₀}𝔠, P^l𝔫, P^k𝔰, P^m𝔯) = b(P^{e₀}, P^l, P^k, P^m) b(𝔠, 𝔫, 𝔰, 𝔯)`: `ϑ` is completely
multiplicative; `γ₂` and `F` split by (3.10) and `poissonFactor_mul`; with `a = χ_P(gen 𝔠)`,
`w = χ_P(gen 𝔠𝔫³) = a b³`, `σ = χ_P(gen 𝔰)`, `t = e₀ + 3l` the cross factors are
`a^{4e₀}` and `w^{2t}`, whose product is `1`.
-/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F]

/-- `HypChi` for all moduli divisible by the small primes. -/
def HypChiAll (F : Type*) [Field F] [NumberField F] (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → HypChi ι 𝔪

variable {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

end C3M

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3M_Chk: `HypChi` from section A's `χ_P` (`C3I_Char`), and CutMul

Exterior primes are `C3I.Good` once `N₀ ≥ max(3^[F:ℚ], N 𝔇)`: `12 ∣ N P − 1` because `μ₁₂ ⊂ F`
and `P ∤ 6`, and `P ∤ 𝔇` because `N P > N 𝔇`.
-/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F]

/-- In `ℚ(μ_n)` with `12 ∣ n`, a prime of norm `> 3^[F:ℚ]` has `12 ∣ N P − 1`. -/
theorem twelve_dvd_absNorm_sub_one (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    [IsCyclotomicExtension {n} ℚ F]
    (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hQ : 3 ^ Module.finrank ℤ (𝓞 F) < Ideal.absNorm P) : 12 ∣ Ideal.absNorm P - 1 := by
  have : P.IsMaximal := hP.isMaximal hP0
  let _ := Ideal.Quotient.field P
  have : Finite (𝓞 F ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP0
  let _ : Fintype (𝓞 F ⧸ P) := Fintype.ofFinite _
  set Q := Ideal.absNorm P
  have hd : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
  have h23 : 2 ^ Module.finrank ℤ (𝓞 F) ≤ 3 ^ Module.finrank ℤ (𝓞 F) :=
    Nat.pow_le_pow_left (by norm_num) _
  have h3le : 3 ≤ 3 ^ Module.finrank ℤ (𝓞 F) := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hd
  have h2 : ¬ 2 ∣ Q := fun h => by
    have := C3B.absNorm_le_of_prime_dvd 2 Nat.prime_two P hP0 h; omega
  have h3 : ¬ 3 ∣ Q := fun h => by
    have := C3B.absNorm_le_of_prime_dvd 3 Nat.prime_three P hP0 h; omega
  have hcop : Q.Coprime 12 := by
    have c2 : Q.Coprime 2 :=
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2))
    have c3 : Q.Coprime 3 :=
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3))
    have : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
    rw [this]; exact Nat.Coprime.mul_right (Nat.Coprime.pow_right 2 c2) c3
  have : NeZero n := ⟨hn0.ne'⟩
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ F
  have hζ12 : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F ^ (n / 12)) 12 :=
    hζ.pow hn0 (Nat.div_mul_cancel hn).symm
  have hω : IsPrimitiveRoot hζ12.toInteger 12 := hζ12.toInteger_isPrimitiveRoot
  have hωb : IsPrimitiveRoot (Ideal.Quotient.mk P hζ12.toInteger) 12 :=
    hω.idealQuotient_mk (by omega) hcop
  have h1 : Ideal.Quotient.mk P hζ12.toInteger ^ (Q - 1) = 1 := by
    rw [show Q = Fintype.card (𝓞 F ⧸ P) from (C3B.card_quot P hP0).symm]
    exact FiniteField.pow_card_sub_one_eq_one _ (hωb.ne_zero (by norm_num))
  exact (hωb.pow_eq_one_iff_dvd _).mp h1

/-- `HypChi` holds for every modulus divisible by the primes of norm `≤ max(3^[F:ℚ], N 𝔇)`. -/
theorem hypChiAll (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) : HypChiAll F ι := by
  refine ⟨max (3 ^ Module.finrank ℤ (𝓞 F)) (Ideal.absNorm (differentIdeal ℤ (𝓞 F))),
    fun 𝔪 _ hS P hP hPe => ?_⟩
  have h𝔪 : ¬ 𝔪 ≤ P := by
    intro h
    apply hP.ne_top
    rw [eq_top_iff, ← hPe.2]
    exact sup_le le_rfl h
  have hgt : max (3 ^ Module.finrank ℤ (𝓞 F)) (Ideal.absNorm (differentIdeal ℤ (𝓞 F))) <
      Ideal.absNorm P := by
    by_contra hc
    exact h𝔪 (hS P hP hPe.1 (not_lt.mp hc))
  let v : HeightOneSpectrum (𝓞 F) := ⟨P, hP, hPe.1⟩
  have hdiff : ¬ differentIdeal ℤ (𝓞 F) ≤ P := by
    intro hle
    have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
    have hD0 : Ideal.absNorm (differentIdeal ℤ (𝓞 F)) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact differentIdeal_ne_bot
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hD0) hdvd
    have := le_max_right (3 ^ Module.finrank ℤ (𝓞 F)) (Ideal.absNorm (differentIdeal ℤ (𝓞 F)))
    omega
  have hgood : C3I.Good 𝔪 v :=
    ⟨hPe.2, twelve_dvd_absNorm_sub_one n hn0 hn P hP hPe.1 (lt_of_le_of_lt (le_max_left _ _) hgt),
      hdiff⟩
  have : NeZero n := ⟨hn0.ne'⟩
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ F
  have hζ6 : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F ^ (n / 6)) 6 :=
    hζ.pow hn0 (Nat.div_mul_cancel (Nat.dvd_trans (by norm_num) hn)).symm
  have hω : IsPrimitiveRoot hζ6.toInteger 6 := hζ6.toInteger_isPrimitiveRoot
  have e : ∀ z : SInt 𝔪, C3I.chi ι hgood hω (Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) z) =
      sexticResidueSymbol ι 𝔪 P z := fun z => C3I.chi_mk hgood hω z
  refine ⟨fun x y => ?_, fun x hx => ?_⟩
  · have h : C3I.chi ι hgood hω (Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x *
        Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) y) =
        C3I.chi ι hgood hω (Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x) *
          C3I.chi ι hgood hω (Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) y) :=
      map_mul _ _ _
    rw [← map_mul, e, e, e] at h
    exact h
  · have hne : Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x ≠ 0 := by
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    have h := C3I.chi_pow_six_apply (ι := ι) hgood hω hne
    rwa [e] at h

end C3M

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3V_LocPf: proof of the local statement `L3V_LocPkg` (Lemma 6.2 and the local symbols) -/

set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

open L3V

theorem L3V_locPkg (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    L3V_LocPkg n F ι := by
  unfold L3V_LocPkg
  obtain ⟨N₂, hN₂⟩ := C3M.hypChiAll n hn0 hn ι
  refine ⟨max N₂ (C3I.cutN F), fun 𝔪 h𝔪 hs g => ?_⟩
  dsimp only
  intro P hP hPe
  obtain ⟨ω, hω⟩ := C3I.exists_prim_six n hn0 hn (F := F)
  set v : HeightOneSpectrum (𝓞 F) := ⟨P, hP, hPe.1⟩
  have hg : C3I.Good 𝔪 v := C3I.good_of_exterior n hn0 hn (le_max_right _ _) hs hP hPe
  have hχ := hN₂ 𝔪 h𝔪 (fun Q hQ hQ0 hle => hs Q hQ hQ0 (hle.trans (le_max_left _ _))) P hP hPe
  haveI := C3I.finite_L hg
  letI := Fintype.ofFinite (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  refine ⟨hχ.1, hχ.2, fun y => ⟨fun hy => C3I.val_eq_one_of_not_mem hg hy, fun h hm => ?_⟩,
    fun I hI => val_gen_eq hg g I hI, fun t t' ht ht' => ?_, fun t ht => ?_, fun y hy => ?_,
    fun k hk e₀ t => Eloc_split (h := hg) (hω := hω) (g := g) hk e₀ t,
    fun j hj => mask_zero_of_ne (h := hg) (hω := hω) (g := g) hj,
    fun j hj e₀ he t ht => ?_,
    fun e₀ he t ht => Rsum_one_vanish (h := hg) (hω := hω) (g := g) he ht,
    fun j hj e₀ he => norm_Rsum_one_le (h := hg) (hω := hω) (g := g) hj he,
    fun j => norm_mask_zero_le (h := hg) (hω := hω) (g := g) j,
    (norm_gaussPhase_two (h := hg) (hω := hω) (g := g)).le⟩
  · have := (mem_iff_val hg.notS y).1 hm
    rw [h] at this
    exact absurd this (not_le.2 exp_neg_one_lt_one)
  · change localSymbol ι 𝔪 v.asIdeal (t * t') =
      localSymbol ι 𝔪 v.asIdeal t * localSymbol ι 𝔪 v.asIdeal t'
    rw [localSymbol_eq hg hω, localSymbol_eq hg hω, localSymbol_eq hg hω,
      res_mul hg.notS ht.le ht'.le, map_mul]
  · change localSymbol ι 𝔪 v.asIdeal t ^ 6 = 1
    rw [localSymbol_eq hg hω]
    exact C3I.chi_pow_six_apply hg hω (res_ne_zero_of_val_eq_one hg.notS ht)
  · change localSymbol ι 𝔪 v.asIdeal (y : F) = _
    rw [localSymbol_eq hg hω, res_of_SInt hg.notS, C3I.chi_mk hg hω]
  · have h1 := Rsum_monomial (h := hg) (hω := hω) (g := g) (j := j) he ht
    rw [← localSymbol_eq hg hω] at h1
    exact h1

end ArtinPrimitiveRoots

end
end

section
section
namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

/-! L3V: Cut63V (`exists_cutoff_exists_mellin_thetaAverage_eq_tsum`, Lemma 6.3 before the radial
smoothing) from the candidate cut `exists_cutoff_exists_mellin_thetaAverage_eq_tsum_localWhittaker`
(the integrated cubic-theta functional equation with the paper's local Whittaker data), whose
statement is `L3V_CutKP` with the house argument order. -/

/-- The candidate cut's statement is `L3V_CutKP`. -/
theorem L3V_cutKP_of_stub (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    L3V_CutKP n F ι :=
  exists_cutoff_exists_mellin_thetaAverage_eq_tsum_localWhittaker n hn0 hn F ι

open Classical in
theorem exists_cutoff_exists_mellin_thetaAverage_eq_tsum (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
  let βp : ℝ → ℕ → ℝ := fun q e =>
    if e = 0 then 1
    else if e % 3 = 1 then q ^ (-((e / 3 : ℕ) : ℝ))
    else if e % 3 = 0 then q ^ ((1 : ℝ) / 2 - ((e / 3 : ℕ) : ℝ))
    else 0
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪),
    ∃ (V : ℝ → ℝ) (rr : ℕ) (C₀ A₀ : ℝ), Measurable V ∧ 0 < C₀ ∧ 0 < A₀ ∧
      (∀ s : ℂ, -(5 / 6 : ℝ) < s.re →
        MellinConvergent (fun t => (V t : ℂ)) s ∧
        mellin (fun t => (V t : ℂ)) s =
          (C₀ : ℂ) * (A₀ : ℂ) ^ s * (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ rr) ∧
    ∃ (T : Type) (_ : Fintype T)
      (ω : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T → ℂ)
      (ρ : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T →
        Ideal (𝓞 F) → ℂ)
      (lam : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T →
        Ideal (𝓞 F) → ℂ)
      (H : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T → ℝ → ℂ)
      (α : ℝ), 0 < α ∧
      (∀ υ 𝔥 𝔣 𝔞 𝔫 s, ‖ω υ 𝔥 𝔣 𝔞 𝔫 s‖ ≤
        ∏ P ∈ (normalizedFactors 𝔣).toFinset,
          βp (Ideal.absNorm P) ((normalizedFactors 𝔞).count P)) ∧
      (∀ υ 𝔥 𝔣 𝔞 𝔫 s, (∃ P ∈ normalizedFactors 𝔞, ¬ P ∣ 𝔣) → ω υ 𝔥 𝔣 𝔞 𝔫 s = 0) ∧
      (∀ υ 𝔥 𝔣 𝔞 𝔫 s 𝔡, ‖ρ υ 𝔥 𝔣 𝔞 𝔫 s 𝔡‖ ≤ 1) ∧
      (∀ υ 𝔥 𝔣 𝔞 𝔫 s 𝔠, ‖lam υ 𝔥 𝔣 𝔞 𝔫 s 𝔠‖ ≤ 1) ∧
      (∀ υ 𝔥 𝔣 𝔞 𝔫 s, ContDiff ℝ 2 (fun t => H υ 𝔥 𝔣 𝔞 𝔫 s (Real.exp t))) ∧
      (∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ υ 𝔥 𝔣 𝔞 𝔫 s, ∀ j : ℕ, j ≤ 2 → ∀ t : ℝ,
        ‖iteratedDeriv j (fun t => H υ 𝔥 𝔣 𝔞 𝔫 s (Real.exp t)) t‖ ≤
          C * min (Real.exp (α * t)) (Real.exp (-(N * t)))) ∧
      (∀ (r : RowClass 𝔪) (𝔥 : Ideal (𝓞 F)), 𝔥 * simplePart r.1.1 = r.1.1 →
        ∀ l : ℝ, 0 < l →
        ∑' p : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠} ×
            {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫},
          gaussPhase g 2 p.1.1 /
              ((Real.sqrt (Ideal.absNorm p.1.1) * Ideal.absNorm p.2.1 : ℝ) : ℂ) *
            χ.thetaChar g (p.1.1 * p.2.1 ^ 3) *
            residueSymbol ι 𝔪 (p.1.1 * p.2.1 ^ 3) (rowElt g r) *
            ((V (Ideal.absNorm (p.1.1 * p.2.1 ^ 3) * l) : ℝ) : ℂ) =
          ∑' k : {𝔣 : Ideal (𝓞 F) // Squarefree 𝔣 ∧ 𝔣 * 𝔣 ∣ 𝔥} × {𝔞 : Ideal (𝓞 F) // 𝔞 ≠ ⊥} ×
              {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫} × T,
            ω r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 / (Ideal.absNorm k.2.2.1.1 : ℂ) *
              ρ r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (simplePart r.1.1) *
              ∑' 𝔠 : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠},
                lam r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 𝔠.1 *
                  residueSymbol ι 𝔪 (simplePart r.1.1) (g.gen 𝔠.1) ^ 3 /
                  ((Real.sqrt (Ideal.absNorm 𝔠.1) : ℝ) : ℂ) *
                  H r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2
                    (l⁻¹ * Ideal.absNorm k.2.1.1 * Ideal.absNorm 𝔠.1 *
                        (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3 /
                      ((Ideal.absNorm (simplePart r.1.1) : ℝ) ^ 2 *
                        (Ideal.absNorm k.1.1 : ℝ) ^ 2))) := by
  exact L3V_cut63V_of_cut n hn0 hn F ι (L3V_cutKP_of_stub n hn0 hn F ι) (L3V_locPkg n hn0 hn F ι)

end ArtinPrimitiveRoots

end
end

section
open ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

open Classical in
theorem solution (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
  let βp : ℝ → ℕ → ℝ := fun q e =>
    if e = 0 then 1
    else if e % 3 = 1 then q ^ (-((e / 3 : ℕ) : ℝ))
    else if e % 3 = 0 then q ^ ((1 : ℝ) / 2 - ((e / 3 : ℕ) : ℝ))
    else 0
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪),
    ∃ (V : ℝ → ℝ) (rr : ℕ) (C₀ A₀ : ℝ), Measurable V ∧ 0 < C₀ ∧ 0 < A₀ ∧
      (∀ s : ℂ, -(5 / 6 : ℝ) < s.re →
        MellinConvergent (fun t => (V t : ℂ)) s ∧
        mellin (fun t => (V t : ℂ)) s =
          (C₀ : ℂ) * (A₀ : ℂ) ^ s * (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ rr) ∧
    ∃ (T : Type) (_ : Fintype T)
      (ω : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T → ℂ)
      (ρ : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T →
        Ideal (𝓞 F) → ℂ)
      (lam : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T →
        Ideal (𝓞 F) → ℂ)
      (H : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T → ℝ → ℂ)
      (α : ℝ), 0 < α ∧
      (∀ υ 𝔥 𝔣 𝔞 𝔫 s, ‖ω υ 𝔥 𝔣 𝔞 𝔫 s‖ ≤
        ∏ P ∈ (normalizedFactors 𝔣).toFinset,
          βp (Ideal.absNorm P) ((normalizedFactors 𝔞).count P)) ∧
      (∀ υ 𝔥 𝔣 𝔞 𝔫 s, (∃ P ∈ normalizedFactors 𝔞, ¬ P ∣ 𝔣) → ω υ 𝔥 𝔣 𝔞 𝔫 s = 0) ∧
      (∀ υ 𝔥 𝔣 𝔞 𝔫 s 𝔡, ‖ρ υ 𝔥 𝔣 𝔞 𝔫 s 𝔡‖ ≤ 1) ∧
      (∀ υ 𝔥 𝔣 𝔞 𝔫 s 𝔠, ‖lam υ 𝔥 𝔣 𝔞 𝔫 s 𝔠‖ ≤ 1) ∧
      (∀ υ 𝔥 𝔣 𝔞 𝔫 s, ContDiff ℝ 2 (fun t => H υ 𝔥 𝔣 𝔞 𝔫 s (Real.exp t))) ∧
      (∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ υ 𝔥 𝔣 𝔞 𝔫 s, ∀ j : ℕ, j ≤ 2 → ∀ t : ℝ,
        ‖iteratedDeriv j (fun t => H υ 𝔥 𝔣 𝔞 𝔫 s (Real.exp t)) t‖ ≤
          C * min (Real.exp (α * t)) (Real.exp (-(N * t)))) ∧
      (∀ (r : RowClass 𝔪) (𝔥 : Ideal (𝓞 F)), 𝔥 * simplePart r.1.1 = r.1.1 →
        ∀ l : ℝ, 0 < l →
        ∑' p : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠} ×
            {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫},
          gaussPhase g 2 p.1.1 /
              ((Real.sqrt (Ideal.absNorm p.1.1) * Ideal.absNorm p.2.1 : ℝ) : ℂ) *
            χ.thetaChar g (p.1.1 * p.2.1 ^ 3) *
            residueSymbol ι 𝔪 (p.1.1 * p.2.1 ^ 3) (rowElt g r) *
            ((V (Ideal.absNorm (p.1.1 * p.2.1 ^ 3) * l) : ℝ) : ℂ) =
          ∑' k : {𝔣 : Ideal (𝓞 F) // Squarefree 𝔣 ∧ 𝔣 * 𝔣 ∣ 𝔥} × {𝔞 : Ideal (𝓞 F) // 𝔞 ≠ ⊥} ×
              {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫} × T,
            ω r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 / (Ideal.absNorm k.2.2.1.1 : ℂ) *
              ρ r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (simplePart r.1.1) *
              ∑' 𝔠 : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠},
                lam r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 𝔠.1 *
                  residueSymbol ι 𝔪 (simplePart r.1.1) (g.gen 𝔠.1) ^ 3 /
                  ((Real.sqrt (Ideal.absNorm 𝔠.1) : ℝ) : ℂ) *
                  H r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2
                    (l⁻¹ * Ideal.absNorm k.2.1.1 * Ideal.absNorm 𝔠.1 *
                        (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3 /
                      ((Ideal.absNorm (simplePart r.1.1) : ℝ) ^ 2 *
                        (Ideal.absNorm k.1.1 : ℝ) ^ 2))) := by
  exact ArtinPrimitiveRoots.exists_cutoff_exists_mellin_thetaAverage_eq_tsum n hn0 hn F ι

end
