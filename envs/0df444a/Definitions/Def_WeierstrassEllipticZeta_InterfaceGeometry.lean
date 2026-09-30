-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
-- name    : WeierstrassEllipticZeta_InterfaceGeometry
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-12T20:58:30.142556+00:00
-- url     : https://prove2.me/theorems/c5de8d99-06c8-40db-9d6d-a5535eedab3a
-- title:
--   Elliptic-extension geometry and subgroup bound interfaces
-- statement:
--   The geometry record packages the period pair, normalized sigma differential data, entire projective lift, quasi-period map, graph quotient identification, additive fiber action, differential flow, jet formulas, finite truncation function, and contact-ideal identities.
--
--   For a finite parameter set $X$, the chart predicate applies the fixed chart certificates to both charts of $X+X+X$. The subgroup-bound predicate is the original conclusion: for a positive real constant $C$ there are a subgroup $H$ and exponents $a,b$ of the prescribed projection type, with $b\le2$, such that
--   $$ (U+1)\#(\phi(X)\bmod H)\le C m^a n^b.$$
--   The record does not assume this subgroup bound. It separates geometric inputs, local certificates, and the desired estimate.
-- source:
--   Structural reorganization of the exact open frontier WeierstrassEllipticZeta.spectral_factor_nilradical_multiplicity_obstruction, https://prove2.me/theorems/39b4eb14-daee-45cf-8bec-ecd2560be211. The mathematical setting is Senthil Kumar K (2026), Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. The interfaces and equivalence proofs are derived here, rather than quoted from the article.

import Definitions.Def_WeierstrassEllipticZeta_InterfaceChartCertificate

open WeierstrassEllipticZeta TranscendenceTheory
open scoped Pointwise Classical

namespace WeierstrassEllipticZeta.Frontier

structure Geometry where
  L :
    PeriodPair
  D :
    EllipticSigmaDifferentialData L
  S :
    Fin 5 → ℂ → ℂ
  hS :
    ∀ j, AnalyticOnNhd ℂ (S j) Set.univ
  hS_value :
    ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
    S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
      weierstrassZeta L z,
      L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j
  hS_ne :
    ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0
  η :
    L.lattice →ₗ[ℤ] ℂ
  hη :
    ∀ ω : L.lattice, η ω = zetaQuasiPeriod L ω
  P :
    GraphQuotientExtension L.lattice η ≃ ProjectiveExtensionChartLocus L.g₂ L.g₃
  hP :
    ∀ z u : ℂ, ∃ hv :
      ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
    (P ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
      ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv
  F :
    ProjectiveExtensionFiberModel L.g₂ L.g₃
  hP_action :
    ∀ (u : ℂ) (e : GraphQuotientExtension L.lattice η),
    P (e + extensionInclusion L.lattice η u) = F.action u (P e)
  hflow :
    (∀ z : ℂ, S 0 z ≠ 0 →
      HasDerivAt (fun w => S 1 w / S 0 w) (S 2 z / S 0 z) z ∧
      HasDerivAt (fun w => S 2 w / S 0 w) (6 * (S 1 z / S 0 z) ^ 2 - L.g₂ / 2) z ∧
      HasDerivAt (fun w => S 3 w / S 0 w) (-S 1 z / S 0 z) z) ∧
    (∀ z : ℂ, S 2 z ≠ 0 →
      HasDerivAt (fun w => S 0 w / S 2 w)
        (-6 * (S 1 z / S 2 z) ^ 2 + L.g₂ / 2 * (S 0 z / S 2 z) ^ 2) z ∧
      HasDerivAt (fun w => S 1 w / S 2 w)
        (-(1 / 2 : ℂ) - L.g₂ * (S 0 z / S 2 z) * (S 1 z / S 2 z) -
          3 * L.g₃ / 2 * (S 0 z / S 2 z) ^ 2) z ∧
      HasDerivAt (fun w => S 4 w / S 2 w)
        (-2 * L.g₂ * (S 1 z / S 2 z) ^ 2 -
          3 * L.g₃ * (S 0 z / S 2 z) * (S 1 z / S 2 z)) z)
  hjets :
    (∀ c : Fin 2, extensionChartDerivation L.g₂ L.g₃ c (extensionChartCubic L.g₂ L.g₃ c) = 0) ∧
    ∀ (c : Fin 2) (p : MvPolynomial (Fin 4) ℂ) (n : ℕ),
      ((extensionChartDerivation L.g₂ L.g₃ c)^[n] p).totalDegree ≤ p.totalDegree + n ∧
      ∀ z : ℂ, S (extensionChartDenominator c) z ≠ 0 →
        iteratedDeriv n (fun w => MvPolynomial.eval (extensionChartCoordinates S c w) p) z =
          MvPolynomial.eval (extensionChartCoordinates S c z)
            ((extensionChartDerivation L.g₂ L.g₃ c)^[n] p) ∧
        ((n : ℕ∞) ≤ analyticOrderAt
            (fun w => MvPolynomial.eval (extensionChartCoordinates S c w) p) z ↔
          ∀ k < n, MvPolynomial.eval (extensionChartCoordinates S c z)
            ((extensionChartDerivation L.g₂ L.g₃ c)^[k] p) = 0)
  B :
    ℕ → ℕ
  hB :
    Monotone B ∧ (∀ d : ℕ, 0 < B d) ∧
    ∀ (d : ℕ) (c : Fin 2) (p : MvPolynomial (Fin 4) ℂ), p.totalDegree ≤ d →
      ∀ v : Fin 4 → ℂ,
        ((∀ k < B d, MvPolynomial.eval v ((extensionChartDerivation L.g₂ L.g₃ c)^[k] p) = 0) ↔
          ∀ k : ℕ, MvPolynomial.eval v ((extensionChartDerivation L.g₂ L.g₃ c)^[k] p) = 0)
  hcontact :
    (∀ (c : Fin 2) (v : Fin 4 → ℂ) (n : ℕ) (p : MvPolynomial (Fin 4) ℂ),
      p ∈ extensionChartContactIdeal L.g₂ L.g₃ c v n ↔
        ∀ k < n, MvPolynomial.eval v ((extensionChartDerivation L.g₂ L.g₃ c)^[k] p) = 0) ∧
    (∀ (c : Fin 2) (v : Fin 4 → ℂ) (m n : ℕ),
      extensionChartContactIdeal L.g₂ L.g₃ c v m * extensionChartContactIdeal L.g₂ L.g₃ c v n ≤
        extensionChartContactIdeal L.g₂ L.g₃ c v (m + n)) ∧
    (∀ (c : Fin 2) (v : Fin 4 → ℂ) (n : ℕ),
      RingHom.ker (MvPolynomial.eval v) ^ n ≤ extensionChartContactIdeal L.g₂ L.g₃ c v n) ∧
    (∀ (c : Fin 2) (v : Fin 4 → ℂ) (n : ℕ), 0 < n →
      (extensionChartContactIdeal L.g₂ L.g₃ c v n).radical = RingHom.ker (MvPolynomial.eval v) ∧
        (extensionChartContactIdeal L.g₂ L.g₃ c v n).IsPrimary) ∧
    (∀ (c : Fin 2) (v w : Fin 4 → ℂ), v ≠ w → ∀ m n : ℕ,
      extensionChartContactIdeal L.g₂ L.g₃ c v m ⊔ extensionChartContactIdeal L.g₂ L.g₃ c w n = ⊤) ∧
    (∀ (c : Fin 2) (v : Fin 4 → ℂ) (n : ℕ) (p : MvPolynomial (Fin 4) ℂ),
      p ∈ extensionChartContactIdeal L.g₂ L.g₃ c v (n + 1) →
        extensionChartDerivation L.g₂ L.g₃ c p ∈ extensionChartContactIdeal L.g₂ L.g₃ c v n) ∧
    (∀ (c : Fin 2) (V : Finset (Fin 4 → ℂ)) (n : V → ℕ)
        (p : V → MvPolynomial (Fin 4) ℂ),
      ∃ q : MvPolynomial (Fin 4) ℂ, ∀ v : V,
        q - p v ∈ extensionChartContactIdeal L.g₂ L.g₃ c v.val (n v))

def HasChartCertificates (G : Geometry) (m n U : ℕ)
    (X : Finset ℂ) (Q : MvPolynomial (Fin 7) ℂ) : Prop :=
  ∀ c : Fin 2,
  let Z := (X + X + X).filter (fun z => G.S (extensionChartDenominator c) z ≠ 0)
  let V := Z.image (extensionChartCoordinates G.S c)
  let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
    ⨅ v : V, extensionChartContactIdeal G.L.g₂ G.L.g₃ c v.val (3 * U + 1)
  ChartCertificate G.L G.B m n U Q c Z V I

def SubgroupBound (G : Geometry) (C : ℝ) (m n U : ℕ) (X : Finset ℂ) : Prop :=
  ∃ H : Submodule ℤ (GraphExtensionGroup G.L.lattice G.η), ∃ a b : ℕ,
  ((a = 1 ∧ H ≤ LinearMap.ker (extensionAdditiveProjection G.L.lattice G.η)) ∨
    (a = 0 ∧ H ≤ LinearMap.ker (extensionEllipticProjection G.L.lattice G.η))) ∧
  b ≤ 2 ∧
  ((U + 1 : ℕ) : ℝ) *
    (H.mkQ '' (extensionCurve G.L.lattice G.η '' (X : Set ℂ))).ncard ≤
    C * (m : ℝ) ^ a * (n : ℝ) ^ b

end WeierstrassEllipticZeta.Frontier


