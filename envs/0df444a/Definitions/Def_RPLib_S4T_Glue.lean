-- Prove2me | Definitions.Def_RPLib_S4T_Glue
-- name    : RPLib_S4T_Glue
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-16T07:14:51.909199+00:00
-- url     : https://prove2.me/theorems/8c672d0b-730b-4040-a481-9e951dd7a8b0
-- title:
--   Tate's isogeny theorem over finite fields (prime-to-$p$ form), library: glue skeleton reducing the theorem to the FLT-project statements and five route lemmas
-- statement:
--   Glue skeleton reducing the theorem to the FLT-project statements and five route lemmas.
--
--   Tate's isogeny theorem `RPLib.DWS.TateIsogenyPrimeToP.{0}` (and the platform leaf 9b26707e, same statement at
--   `F : Type`) from
--
--   * the Proved FLT-project theorems, taken as hypotheses `h_<id8> : FLT.S_<id8>` (byte-exact statements, see
--     `scratch/rp/lib/S4T/FLTStmts.lean`; locally they are sorry stubs, so they are NEVER used as lemmas), and
--   * our new lemmas, stated here as `Prop`s `L0Stmt`, `L2Stmt`, `L5Stmt`, `L7Stmt`, `L9Stmt` (route
--     `scratch/rp/S4T_ROUTE.md` section 3: L4 is folded into `L5Stmt`, L6 (repair R3) into `L7Stmt`). Each later unit
--     proves one of them, taking the FLT statements it uses as explicit hypotheses.
--
--   Chain: L0 (setup over the residue field `k` of a valuation subring `A` of `Q̄`) -> 2bb50ff6 (nonzero p-torsion
--   `T`) -> 0cf211ae (Deuring lift `α` of the Frobenius, twice) -> L2 (char poly of `α`, `α` and `t - α` of infinite
--   order) -> 0b434d80 (char-0 isogeny `β ≠ 0`) -> L5 (prime-to-`p` pair `u, w`, `w ∘ u = N`) -> cd49331c (reductions
--   `νu, νw`, twice) -> L7 (`ū, w̄` over `k`, Frobenius-equivariant, `w̄ ∘ ū = N`) -> 7b2524b2 (descent to
--   `F`-coefficients, twice) -> L9 (function-field bridge) -> conclusion.
--
--   **Formalization note.** Library module of a formalization of Tate's isogeny theorem over finite fields in prime-to-$p$ form (ordinary elliptic curves with the same number of points are linked by $F$-isogenies $u, w$ with $w \circ u = [N]$, $p \nmid N$, stated through $F$-algebra maps of function fields), via Deuring lifting to characteristic $0$. It is conditional only on fifteen Proved prove2.me theorems of the FLT project, which enter as explicit hypotheses whose types are their exact statements (never as lemmas). Part of a formalization of the Ramanujan-Petersson conjecture in weight two. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144, Theorem 1; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560, Chapter 4; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Sections III.6-III.7

import Mathlib
import Definitions.Def_RPLib_S4T_FLTStmts
import Definitions.Def_RPLib_S3_TateStmtP

/-!
# S4T glue skeleton (S4T-Spike task 2)

Tate's isogeny theorem `RPLib.DWS.TateIsogenyPrimeToP.{0}` (and the platform leaf 9b26707e, same statement at
`F : Type`) from

* the Proved FLT-project theorems, taken as hypotheses `h_<id8> : FLT.S_<id8>` (byte-exact statements, see
  `scratch/rp/lib/S4T/FLTStmts.lean`; locally they are sorry stubs, so they are NEVER used as lemmas), and
* our new lemmas, stated here as `Prop`s `L0Stmt`, `L2Stmt`, `L5Stmt`, `L7Stmt`, `L9Stmt` (route
  `scratch/rp/S4T_ROUTE.md` section 3: L4 is folded into `L5Stmt`, L6 (repair R3) into `L7Stmt`). Each later unit
  proves one of them, taking the FLT statements it uses as explicit hypotheses.

Chain: L0 (setup over the residue field `k` of a valuation subring `A` of `Q̄`) -> 2bb50ff6 (nonzero p-torsion
`T`) -> 0cf211ae (Deuring lift `α` of the Frobenius, twice) -> L2 (char poly of `α`, `α` and `t - α` of infinite
order) -> 0b434d80 (char-0 isogeny `β ≠ 0`) -> L5 (prime-to-`p` pair `u, w`, `w ∘ u = N`) -> cd49331c (reductions
`νu, νw`, twice) -> L7 (`ū, w̄` over `k`, Frobenius-equivariant, `w̄ ∘ ū = N`) -> 7b2524b2 (descent to
`F`-coefficients, twice) -> L9 (function-field bridge) -> conclusion.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedVariables false

namespace RPLib.S4T.Glue

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing

/-- **L0 Setup.** A valuation subring `A ⊆ Q̄` with residue field `k` of characteristic `p = ringChar F`,
algebraically closed, an `F`-algebra, the `q`-power Frobenius `σ` of `k / F`, `t q` with no integer root of
`m² - t m + q`, `q` a positive power of `p`, `p ∤ t`, and for both curves the Frobenius `Point.map σ` is a
`k`-rational endomorphism of `W_k` with `π² + q = t π`. -/
def L0Stmt : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (W W' : WeierstrassCurve F) [W.IsElliptic] [W'.IsElliptic],
    Nat.card W.toAffine.Point = Nat.card W'.toAffine.Point →
    ¬ ((ringChar F : ℤ) ∣ ((Fintype.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ))) →
    ∃ (A : ValuationSubring (AlgebraicClosure ℚ)) (_ : CharP (ResidueField A) (ringChar F))
      (_ : IsAlgClosed (ResidueField A)) (_ : Algebra F (ResidueField A))
      (σ : ResidueField A ≃ₐ[F] ResidueField A) (t q : ℤ),
      (∀ x, σ x = x ^ Fintype.card F) ∧ (∀ m : ℤ, m ^ 2 - t * m + q ≠ 0) ∧
      (∃ n : ℕ, 0 < n ∧ q = (ringChar F : ℤ) ^ n) ∧ ¬ ((ringChar F : ℤ) ∣ t) ∧
      ∀ [DecidableEq (ResidueField A)],
        (Point.map (W' := W) σ.toAlgHom ∈
            rationalHomSet (ResidueField A) (W.baseChange (ResidueField A)) (W.baseChange (ResidueField A)) ∧
          (Point.map (W' := W) σ.toAlgHom).comp (Point.map (W' := W) σ.toAlgHom) + q • AddMonoidHom.id _ =
            t • Point.map (W' := W) σ.toAlgHom) ∧
        (Point.map (W' := W') σ.toAlgHom ∈
            rationalHomSet (ResidueField A) (W'.baseChange (ResidueField A)) (W'.baseChange (ResidueField A)) ∧
          (Point.map (W' := W') σ.toAlgHom).comp (Point.map (W' := W') σ.toAlgHom) + q • AddMonoidHom.id _ =
            t • Point.map (W' := W') σ.toAlgHom)

/-- **L2 red_inj consequences** for one curve. The Deuring lift `α` (output of 0cf211ae for `π = Point.map σ`)
satisfies `α² + q = t α`, and neither `α` nor `t - α` has finite order (repair R2's downstairs input). -/
def L2Stmt : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (W : WeierstrassCurve F) [W.IsElliptic]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [DecidableEq (AlgebraicClosure ℚ)]
    [DecidableEq (ResidueField A)] [CharP (ResidueField A) (ringChar F)] [IsAlgClosed (ResidueField A)]
    [Algebra F (ResidueField A)] (σ : ResidueField A ≃ₐ[F] ResidueField A)
    (hσ : ∀ x, σ x = x ^ Fintype.card F) (t q : ℤ) (hirr : ∀ m : ℤ, m ^ 2 - t * m + q ≠ 0)
    (hq : ∃ n : ℕ, 0 < n ∧ q = (ringChar F : ℤ) ^ n) (ht : ¬ ((ringChar F : ℤ) ∣ t))
    (hπ : Point.map (W' := W) σ.toAlgHom ∈
      rationalHomSet (ResidueField A) (W.baseChange (ResidueField A)) (W.baseChange (ResidueField A)))
    (hπch : (Point.map (W' := W) σ.toAlgHom).comp (Point.map (W' := W) σ.toAlgHom) + q • AddMonoidHom.id _ =
      t • Point.map (W' := W) σ.toAlgHom)
    (T : (W.baseChange (ResidueField A)).toAffine.Point) (hT0 : T ≠ 0) (hpT : ringChar F • T = 0)
    (E : WeierstrassCurve A) (hΔ : (E.map (residue A)).Δ ≠ 0) (v : VariableChange (ResidueField A))
    (hv : v • E.map (residue A) = W.baseChange (ResidueField A))
    {α : (E.map A.subtype).toAffine.Point →+ (E.map A.subtype).toAffine.Point}
    (hα : α ∈ rationalHomSet (AlgebraicClosure ℚ) (E.map A.subtype) (E.map A.subtype))
    (hcompat : ∀ P : (E.map A.subtype).toAffine.Point,
      (Point.equivOfVariableChangeEq hv).symm (reduceHom hΔ (α P)) =
        Point.map (W' := W) σ.toAlgHom ((Point.equivOfVariableChangeEq hv).symm (reduceHom hΔ P))),
    α.comp α + q • AddMonoidHom.id (E.map A.subtype).toAffine.Point = t • α ∧
      ∀ m : ℕ, 0 < m → (⇑α)^[m] ≠ id ∧ (⇑(t • AddMonoidHom.id (E.map A.subtype).toAffine.Point - α))^[m] ≠ id

/-- **L4 + L5 prime-to-`p` in characteristic 0** (repairs R1, R2; no Vélu quotient). From a nonzero rational
`β : X₁ → X₂` between curves whose rational endomorphisms `α_i` satisfy `x² - t x + q` (`q` a power of `p`,
`p ∤ t`, `α₁` and `t - α₁` of infinite order), a rational pair `u, w` with `w ∘ u = N = u ∘ w`, `p ∤ N`. -/
def L5Stmt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure ℚ)]
    (X₁ X₂ : WeierstrassCurve (AlgebraicClosure ℚ)) [X₁.IsElliptic] [X₂.IsElliptic]
    (t q : ℤ) (hirr : ∀ m : ℤ, m ^ 2 - t * m + q ≠ 0) (hq : ∃ n : ℕ, 0 < n ∧ q = (p : ℤ) ^ n)
    (ht : ¬ (p : ℤ) ∣ t)
    {α₁ : X₁.toAffine.Point →+ X₁.toAffine.Point} {α₂ : X₂.toAffine.Point →+ X₂.toAffine.Point}
    (hα₁ : α₁ ∈ rationalHomSet (AlgebraicClosure ℚ) X₁ X₁)
    (hα₂ : α₂ ∈ rationalHomSet (AlgebraicClosure ℚ) X₂ X₂)
    (h₁ : α₁.comp α₁ + q • AddMonoidHom.id X₁.toAffine.Point = t • α₁)
    (h₂ : α₂.comp α₂ + q • AddMonoidHom.id X₂.toAffine.Point = t • α₂)
    (hinf₁ : ∀ m : ℕ, 0 < m → (⇑α₁)^[m] ≠ id ∧ (⇑(t • AddMonoidHom.id X₁.toAffine.Point - α₁))^[m] ≠ id)
    {β : X₁.toAffine.Point →+ X₂.toAffine.Point} (hβ : β ∈ rationalHomSet (AlgebraicClosure ℚ) X₁ X₂)
    (hβ0 : β ≠ 0),
    ∃ u : X₁.toAffine.Point →+ X₂.toAffine.Point, u ∈ rationalHomSet (AlgebraicClosure ℚ) X₁ X₂ ∧
      ∃ w : X₂.toAffine.Point →+ X₁.toAffine.Point, w ∈ rationalHomSet (AlgebraicClosure ℚ) X₂ X₁ ∧
        ∃ N : ℕ, ¬ p ∣ N ∧ w.comp u = (N : ℤ) • AddMonoidHom.id X₁.toAffine.Point ∧
          u.comp w = (N : ℤ) • AddMonoidHom.id X₂.toAffine.Point

/-- **L6 (repair R3) + L7 Frobenius-equivariance + transport to `W_k`.** The reductions `νu, νw` (outputs of
cd49331c for `u, w`), moved to `W_k, W'_k` through the variable changes `v, v'`, give `k`-rational `ū, w̄`
commuting with the Frobenius `σ` and with `w̄ ∘ ū = N`. -/
def L7Stmt : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (W W' : WeierstrassCurve F) [W.IsElliptic] [W'.IsElliptic]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [DecidableEq (AlgebraicClosure ℚ)]
    [DecidableEq (ResidueField A)] [CharP (ResidueField A) (ringChar F)] [IsAlgClosed (ResidueField A)]
    [Algebra F (ResidueField A)] (σ : ResidueField A ≃ₐ[F] ResidueField A)
    (hσ : ∀ x, σ x = x ^ Fintype.card F) (t q : ℤ) (hirr : ∀ m : ℤ, m ^ 2 - t * m + q ≠ 0)
    (hq : ∃ n : ℕ, 0 < n ∧ q = (ringChar F : ℤ) ^ n) (ht : ¬ ((ringChar F : ℤ) ∣ t))
    (hπ : Point.map (W' := W) σ.toAlgHom ∈
      rationalHomSet (ResidueField A) (W.baseChange (ResidueField A)) (W.baseChange (ResidueField A)))
    (hπch : (Point.map (W' := W) σ.toAlgHom).comp (Point.map (W' := W) σ.toAlgHom) + q • AddMonoidHom.id _ =
      t • Point.map (W' := W) σ.toAlgHom)
    (hπ' : Point.map (W' := W') σ.toAlgHom ∈
      rationalHomSet (ResidueField A) (W'.baseChange (ResidueField A)) (W'.baseChange (ResidueField A)))
    (hπch' : (Point.map (W' := W') σ.toAlgHom).comp (Point.map (W' := W') σ.toAlgHom) +
      q • AddMonoidHom.id _ = t • Point.map (W' := W') σ.toAlgHom)
    (T : (W.baseChange (ResidueField A)).toAffine.Point) (hT0 : T ≠ 0) (hpT : ringChar F • T = 0)
    (T' : (W'.baseChange (ResidueField A)).toAffine.Point) (hT0' : T' ≠ 0) (hpT' : ringChar F • T' = 0)
    (E E' : WeierstrassCurve A) (hΔ : (E.map (residue A)).Δ ≠ 0) (hΔ' : (E'.map (residue A)).Δ ≠ 0)
    (v v' : VariableChange (ResidueField A))
    (hv : v • E.map (residue A) = W.baseChange (ResidueField A))
    (hv' : v' • E'.map (residue A) = W'.baseChange (ResidueField A))
    {u : (E.map A.subtype).toAffine.Point →+ (E'.map A.subtype).toAffine.Point}
    {w : (E'.map A.subtype).toAffine.Point →+ (E.map A.subtype).toAffine.Point}
    (hu : u ∈ rationalHomSet (AlgebraicClosure ℚ) (E.map A.subtype) (E'.map A.subtype))
    (hw : w ∈ rationalHomSet (AlgebraicClosure ℚ) (E'.map A.subtype) (E.map A.subtype))
    (N : ℕ) (hpN : ¬ ringChar F ∣ N) (hwu : w.comp u = (N : ℤ) • AddMonoidHom.id (E.map A.subtype).toAffine.Point)
    (huw : u.comp w = (N : ℤ) • AddMonoidHom.id (E'.map A.subtype).toAffine.Point)
    {νu : (E.map (residue A)).toAffine.Point →+ (E'.map (residue A)).toAffine.Point}
    {νw : (E'.map (residue A)).toAffine.Point →+ (E.map (residue A)).toAffine.Point}
    (hνu : νu ∈ rationalHomSet (ResidueField A) (E.map (residue A)) (E'.map (residue A)))
    (hνw : νw ∈ rationalHomSet (ResidueField A) (E'.map (residue A)) (E.map (residue A)))
    (hredu : (reduceHom hΔ').comp u = νu.comp (reduceHom hΔ))
    (hredw : (reduceHom hΔ).comp w = νw.comp (reduceHom hΔ')),
    ∃ ub : (W.baseChange (ResidueField A)).toAffine.Point →+ (W'.baseChange (ResidueField A)).toAffine.Point,
      ub ∈ rationalHomSet (ResidueField A) (W.baseChange (ResidueField A)) (W'.baseChange (ResidueField A)) ∧
      ∃ wb : (W'.baseChange (ResidueField A)).toAffine.Point →+ (W.baseChange (ResidueField A)).toAffine.Point,
        wb ∈ rationalHomSet (ResidueField A) (W'.baseChange (ResidueField A)) (W.baseChange (ResidueField A)) ∧
        (∀ P : (W.baseChange (ResidueField A)).toAffine.Point, ub (σ • P) = σ • ub P) ∧
        (∀ P : (W'.baseChange (ResidueField A)).toAffine.Point, wb (σ • P) = σ • wb P) ∧
        wb.comp ub = (N : ℤ) • AddMonoidHom.id (W.baseChange (ResidueField A)).toAffine.Point

/-- **L9 function-field bridge** (route C's RevBridge). `F`-rational `u : W → W'`, `w : W' → W` over an
algebraically closed `k ⊇ F` with `w ∘ u = [N]`, `N ≠ 0` in `F`, give the TateStmtP conclusion
(`f = u^*`, `g = w^*`). -/
def L9Stmt : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (W W' : WeierstrassCurve F) [W.IsElliptic] [W'.IsElliptic]
    (k : Type) [Field k] [IsAlgClosed k] [DecidableEq k] [Algebra F k]
    {u : (W.baseChange k).toAffine.Point →+ (W'.baseChange k).toAffine.Point}
    {w : (W'.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point}
    (hu : u ∈ rationalHomSet k W W') (hw : w ∈ rationalHomSet k W' W) (N : ℕ) (hN : (N : F) ≠ 0)
    (hwu : w.comp u = (N : ℤ) • AddMonoidHom.id (W.baseChange k).toAffine.Point),
    ∃ (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
      (g : W.toAffine.FunctionField →ₐ[F] W'.toAffine.FunctionField) (N : ℕ), (N : F) ≠ 0 ∧
      ∃ h : (W.baseChange W.toAffine.FunctionField).toAffine.Nonsingular
          (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
            (CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X)))
          (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
            (CoordinateRing.mk W.toAffine Polynomial.X)),
        Point.map (W' := W.toAffine) (f.comp g) (Point.some _ _ h) = N • Point.some _ _ h

/-- The generic fibre of a curve with good reduction is elliptic. -/
theorem isElliptic_map_subtype {L : Type} [Field L] {A : ValuationSubring L} (E : WeierstrassCurve A)
    (hΔ : (E.map (residue A)).Δ ≠ 0) : (E.map A.subtype).IsElliptic := by
  refine ⟨?_⟩
  rw [WeierstrassCurve.map_Δ, isUnit_iff_ne_zero]
  intro h0
  apply hΔ
  have hE : E.Δ = 0 := Subtype.val_injective (by simpa using h0)
  rw [WeierstrassCurve.map_Δ, hE, map_zero]

/-- **Glue (L10 assembly).** Tate's isogeny theorem from the FLT statements and L0, L2, L5, L7, L9. -/
theorem tate_of_FLT (h0cf : FLT.S_0cf211ae) (h0b4 : FLT.S_0b434d80.{0}) (hcd4 : FLT.S_cd49331c.{0})
    (h7b2 : FLT.S_7b2524b2.{0, 0}) (h2bb : FLT.S_2bb50ff6.{0})
    (hL0 : L0Stmt) (hL2 : L2Stmt) (hL5 : L5Stmt) (hL7 : L7Stmt) (hL9 : L9Stmt) :
    RPLib.DWS.TateIsogenyPrimeToP.{0} := by
  intro F _ _ W W' _ _ hcard hord
  obtain ⟨A, _, _, _, σ, t, q, hσ, hirr, hq, ht, hfrob⟩ := hL0 F W W' hcard hord
  letI : DecidableEq (ResidueField A) := Classical.decEq _
  haveI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F (ringChar F)⟩
  obtain ⟨⟨hπ, hπch⟩, ⟨hπ', hπch'⟩⟩ := hfrob
  have hqd : ((ringChar F : ℕ) : ℤ) ∣ q := by
    obtain ⟨n, hn, rfl⟩ := hq
    exact dvd_pow_self _ hn.ne'
  haveI : (W.baseChange (ResidueField A)).IsElliptic :=
    inferInstanceAs (W.map (algebraMap F (ResidueField A))).IsElliptic
  haveI : (W'.baseChange (ResidueField A)).IsElliptic :=
    inferInstanceAs (W'.map (algebraMap F (ResidueField A))).IsElliptic
  -- nonzero p-torsion on both curves (2bb50ff6)
  obtain ⟨T, hT0, hpT⟩ := h2bb (ringChar F) (W.baseChange (ResidueField A)) hπ t q hπch hirr hqd ht
  obtain ⟨T', hT0', hpT'⟩ := h2bb (ringChar F) (W'.baseChange (ResidueField A)) hπ' t q hπch' hirr hqd ht
  -- Deuring lifts of the Frobenius (0cf211ae)
  obtain ⟨E, hΔ, v, hv, α, hα, hcompat⟩ := h0cf (ringChar F) A (W.baseChange (ResidueField A)) hπ
  obtain ⟨E', hΔ', v', hv', α', hα', hcompat'⟩ := h0cf (ringChar F) A (W'.baseChange (ResidueField A)) hπ'
  haveI := isElliptic_map_subtype E hΔ
  haveI := isElliptic_map_subtype E' hΔ'
  -- L2: char poly of the lifts, infinite order
  obtain ⟨hαch, hαinf⟩ := hL2 F W A σ hσ t q hirr hq ht hπ hπch T hT0 hpT E hΔ v hv hα hcompat
  obtain ⟨hαch', -⟩ := hL2 F W' A σ hσ t q hirr hq ht hπ' hπch' T' hT0' hpT' E' hΔ' v' hv' hα' hcompat'
  -- char-0 CM isogeny (0b434d80)
  obtain ⟨β, hβ, hβ0⟩ := h0b4 (E.map A.subtype) (E'.map A.subtype) t q hirr hα hα' hαch hαch'
  -- L5: prime-to-p pair
  obtain ⟨u, hu, w, hw, N, hpN, hwu, huw⟩ :=
    hL5 (ringChar F) (E.map A.subtype) (E'.map A.subtype) t q hirr hq ht hα hα' hαch hαch' hαinf hβ hβ0
  -- reductions (cd49331c)
  obtain ⟨νu, hνu, hredu, -⟩ := hcd4 E E' hΔ hΔ' hu
  obtain ⟨νw, hνw, hredw, -⟩ := hcd4 E' E hΔ' hΔ hw
  -- L7: Frobenius-equivariant pair over k
  obtain ⟨ub, hub, wb, hwb, hcu, hcw, hwub⟩ :=
    hL7 F W W' A σ hσ t q hirr hq ht hπ hπch hπ' hπch' T hT0 hpT T' hT0' hpT' E E' hΔ hΔ' v v' hv hv'
      hu hw N hpN hwu huw hνu hνw hredu hredw
  -- descent to F-coefficients (7b2524b2)
  have hubF := h7b2 W W' σ hσ hub hcu
  have hwbF := h7b2 W' W σ hσ hwb hcw
  have hN : (N : F) ≠ 0 := by
    rwa [Ne, CharP.cast_eq_zero_iff F (ringChar F)]
  -- L9: function-field bridge
  exact hL9 F W W' (ResidueField A) hubF hwbF N hN hwub

/-- The platform leaf 9b26707e (`WeierstrassCurve.tate_isogeny_theorem_prime_to_char`), verbatim conclusion. -/
theorem tate_isogeny_theorem_prime_to_char_of_FLT (h0cf : FLT.S_0cf211ae) (h0b4 : FLT.S_0b434d80.{0})
    (hcd4 : FLT.S_cd49331c.{0}) (h7b2 : FLT.S_7b2524b2.{0, 0}) (h2bb : FLT.S_2bb50ff6.{0})
    (hL0 : L0Stmt) (hL2 : L2Stmt) (hL5 : L5Stmt) (hL7 : L7Stmt) (hL9 : L9Stmt)
    (F : Type) [Field F] [Fintype F]
    (W W' : WeierstrassCurve F) [W.IsElliptic] [W'.IsElliptic]
    (hcard : Nat.card W.toAffine.Point = Nat.card W'.toAffine.Point)
    (hord : ¬ ((ringChar F : ℤ) ∣ ((Fintype.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)))) :
    ∃ (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
      (g : W.toAffine.FunctionField →ₐ[F] W'.toAffine.FunctionField) (N : ℕ), (N : F) ≠ 0 ∧
      ∃ h : (W.baseChange W.toAffine.FunctionField).toAffine.Nonsingular
          (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
            (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X)))
          (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
            (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine Polynomial.X)),
        WeierstrassCurve.Affine.Point.map (W' := W.toAffine) (f.comp g)
            (WeierstrassCurve.Affine.Point.some _ _ h) =
          N • WeierstrassCurve.Affine.Point.some _ _ h :=
  tate_of_FLT h0cf h0b4 hcd4 h7b2 h2bb hL0 hL2 hL5 hL7 hL9 F W W' hcard hord

end RPLib.S4T.Glue


