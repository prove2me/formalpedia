-- Prove2me | Definitions.Def_QSDMixing_GU_Supplement_HeckeDualData
-- name    : QSDMixing_GU_Supplement_HeckeDualData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:39:29.583194+00:00
-- url     : https://prove2.me/theorems/ae375b8d-73be-44a4-b209-77d1a49c3619
-- title:
--   Dual hypergroup of a commutative Hecke algebra
-- statement:
--   For a commutative Hecke algebra $\operatorname{End}_G(\mathbb C[G/H])$, **dual-hypergroup data** consist of its primitive orthogonal idempotents $(E_i)$, their positive multiplicities $m_i=\operatorname{tr}(E_i)$, and Krein parameters $q_{ij}^k$ satisfying
--
--   $$
--   E_i\circ E_j=\frac1{|G/H|}\sum_k q_{ij}^kE_k.
--   $$
--
--   The dual convolution is $K_{ij}^k=m_kq_{ij}^k/(m_im_j)$, and the Haar law is $\pi_i=m_i/|G/H|$. The definition records the hypergroup probability, associativity, identity, and stationarity laws. It also defines $\Xi(p)=\sum_i(p_i/m_i)E_i$, convolution powers, and the corresponding total-variation mixing time.
--
--   This is the representation-theoretic object used to turn the Schur-channel walk into the classical walk of Theorem 4.
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), §3.2, pp.19–20, eqs. (80)–(85)

import Mathlib
import Definitions.Def_QSDMixing_GU_hecke
import Definitions.Def_QSDMixing_GU_Supplement_FiniteProbability

set_option autoImplicit false
open scoped MatrixOrder ComplexOrder

namespace QSDMixing.GU.Supplement

noncomputable local instance heckeDualDecidableEq {α : Type} : DecidableEq α :=
  Classical.decEq α

/-- Primitive-idempotent and Krein-parameter data for the dual hypergroup of a commutative
Hecke algebra. The fields spell out the normalization used in §3.2, equations (80)--(85).

Zhou--Leditzky, *A mixing time method for estimating the sample complexity of quantum state
discrimination*, arXiv:2609.40182 (held version, sha256 62fb68dd…), §3.2, pp.19--20. -/
structure HeckeDualData {G : Type} [Group G] [Finite G] (H : Subgroup G)
    (Ω : Type) [Fintype Ω] where
  E : Ω → Matrix (G ⧸ H) (G ⧸ H) ℂ
  m : Ω → ℝ
  q : Ω → Ω → Ω → ℝ
  identity : Ω
  E_mem : ∀ i, E i ∈ QSDMixing.GU.hecke H
  E_pos : ∀ i, (E i).PosSemidef
  E_mul : ∀ i j, E i * E j = if i = j then E i else 0
  E_sum : ∑ i, E i = 1
  primitive : ∀ i (P : Matrix (G ⧸ H) (G ⧸ H) ℂ),
    P ∈ QSDMixing.GU.hecke H → P * P = P → P * E i = P → P = 0 ∨ P = E i
  m_pos : ∀ i, 0 < m i
  m_trace : ∀ i, Matrix.trace (E i) = (m i : ℂ)
  schur_formula : ∀ i j,
    (fun x y => E i x y * E j x y) =
      (Fintype.card (G ⧸ H) : ℂ)⁻¹ •
        ∑ k, ((q i j k : ℝ) : ℂ) • E k
  conv : Ω → Ω → Ω → ℝ
  conv_formula : ∀ i j k,
    conv i j k = m k * q i j k / (m i * m j)
  conv_nonneg : ∀ i j k, 0 ≤ conv i j k
  conv_sum_one : ∀ i j, ∑ k, conv i j k = 1
  conv_assoc : ∀ i j k l,
    ∑ a, conv i j a * conv a k l = ∑ a, conv j k a * conv i a l
  conv_left_id : ∀ i j, conv identity i j = if i = j then 1 else 0
  conv_right_id : ∀ i j, conv i identity j = if i = j then 1 else 0
  haar : FiniteProbability Ω
  haar_formula : ∀ i, haar i = m i / (Fintype.card (G ⧸ H) : ℝ)
  haar_stationary : ∀ i k, ∑ j, haar j * conv i j k = haar k

/-- The primitive-idempotent map `Ξ(q)=∑ᵢ(qᵢ/mᵢ)Eᵢ`. -/
noncomputable def HeckeDualData.xi {G : Type} [Group G] [Finite G] {H : Subgroup G}
    {Ω : Type} [Fintype Ω] (D : HeckeDualData H Ω) (p : Ω → ℝ) :
    Matrix (G ⧸ H) (G ⧸ H) ℂ :=
  ∑ i, (((p i / D.m i : ℝ) : ℂ)) • D.E i

/-- Convolution of probability laws on the dual hypergroup. -/
noncomputable def HeckeDualData.measureConvolution {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {Ω : Type} [Fintype Ω] (D : HeckeDualData H Ω)
    (p r : Ω → ℝ) (k : Ω) : ℝ :=
  ∑ i, ∑ j, p i * r j * D.conv i j k

/-- The `t`-fold dual-hypergroup convolution power. -/
noncomputable def HeckeDualData.convolutionPower {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {Ω : Type} [Fintype Ω] (D : HeckeDualData H Ω)
    (p : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun z => if z = D.identity then 1 else 0
  | t + 1 => D.measureConvolution (D.convolutionPower p t) p

/-- The total-variation mixing time of the dual-hypergroup walk, starting at its identity. -/
noncomputable def HeckeDualData.mixingTime {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {Ω : Type} [Fintype Ω] (D : HeckeDualData H Ω)
    (p : Ω → ℝ) (ε : ℝ) : ℕ∞ :=
  sInf {T : ℕ∞ | ∃ t : ℕ, 1 ≤ t ∧ T = t ∧
    totalVariation (D.convolutionPower p t) D.haar ≤ ε}

end QSDMixing.GU.Supplement


