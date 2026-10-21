-- Prove2me | Definitions.Def_QRH_lfun
-- name    : QRH_lfun
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-20T12:03:06.0272+00:00
-- url     : https://prove2.me/theorems/74f1011e-1644-4f61-8fd4-40a32b3a787c
-- title:
--   The L-function world: Hecke and Dirichlet L-functions, the base change, and the Mellin data
-- statement:
--   Over a fixed arithmetic world and sums data, the L-function world is the interface for the analytic objects of the source. It carries abstract types of finite-order Hecke characters of K = Q(sqrt(-3)) and of Dirichlet characters with their trivial characters; the coefficients of a Hecke character on the primary elements, completely multiplicative and of modulus one on the elements prime to S; the Hecke and Dirichlet L-functions as abstract functions from C to C; the quadratic base change from Dirichlet to Hecke characters through the norm, the product of Dirichlet characters, the nontrivial character chi_{-3} modulo 3, the Euler factors removed by the base change and nonzero on the half-plane Re s > 0, the base change identity L_K(s, chi o N) = L(s, chi) L(s, chi chi_{-3}) up to those factors away from s = 1 and at s = 1, the triviality transfer, and Dirichlet's nonvanishing theorem L(1, chi_{-3}) != 0; and the Mellin-transform data: the Mellin transform of the smoothed Mobius sums for a Hecke character and a weight, the Mellin transform of the weight, the Euler-product correction L^S = L eS with eS nonzero on the half-plane Re s > 11/12, the nonvanishing of the weight transform on that half-plane, and the conditional Mellin identity: under the power-saving predicate for the coefficient sequence mu nu, the Euler product outside S inverts the smoothed transform on the half-plane. The power-saving predicate MobiusSaving states that for every eps > 0 there is k with |A_1(D)| <= k D^(11/12 + eps) for all D >= 2.
-- source:
--   The Quasi-Riemann Hypothesis, October 2026, Section 3 (the reduction, the Mellin step, and the base change).

import Mathlib
import Definitions.Def_QRH_arith
import Definitions.Def_QRH_sums

universe u

/-!
# The Quasi-Riemann Hypothesis: the L-function world

The L-functions of the source, in the form of an interface: the
finite-order Hecke characters of K = Q(√−3) and the Dirichlet characters
as abstract types, their L-functions as abstract functions, the quadratic
base change with its χ₋₃ twist and the Euler factors it removes,
Dirichlet's nonvanishing theorem at s = 1 for χ₋₃, and the Mellin
transform data through which a power saving for the smoothed Möbius sums
propagates to nonvanishing of the Hecke L-function on the half-plane
Re s > 11/12 (section 3 of the paper). Hecke's meromorphic continuation
and the identity theorem are carried by the Mellin identity field.
-/

namespace QRH

/-- The power-saving estimate for the smoothed twisted Möbius sums
(equation 2.1 of the source): for every ε > 0 the sums A₁(D) satisfy
|A₁(D)| ≤ k · D^(11/12 + ε) for all D ≥ 2. This is the form in which
the mean-square estimate of Proposition 3.1 feeds the zero-free
argument. -/
def MobiusSaving (W : QRHWorld) (S : QRHSums W) (c : W.E → ℂ)
    (Wt : ℝ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ k : ℝ, ∀ D : ℝ, 2 ≤ D →
    ‖A1sum W S c Wt D (2 * D)‖ ≤ k * D ^ (11 / 12 + ε)

/-- The L-function world: the finite-order Hecke characters of
K = Q(√−3) and the Dirichlet characters, their L-functions, the
quadratic base change χ ↦ χ ∘ N with its χ₋₃ twist, the Euler factors
removed by the base change, Dirichlet's nonvanishing theorem for χ₋₃ at
s = 1, and the Mellin-transform data. The fields asserting equations are
the analytic inputs of the source: the base change identity, Dirichlet's
nonvanishing theorem, and the conditional Mellin identity of section 3,
which packages Hecke's meromorphic continuation and the identity
theorem. -/
structure QRHLWorld (W : QRHWorld.{u}) (S : QRHSums W) where
  /-- the finite-order Hecke characters of K -/
  HeckeChi : Type
  /-- the Dirichlet characters -/
  DirChi : Type
  /-- the trivial Hecke character -/
  IsTrivialH : HeckeChi → Prop
  /-- the trivial Dirichlet character -/
  IsTrivialD : DirChi → Prop
  /-- the coefficients of a Hecke character on the primary elements,
  extended by zero outside the conductor -/
  hcoef : HeckeChi → W.E → ℂ
  hcoef_mul : ∀ (ν : HeckeChi) (a b : W.E),
    hcoef ν (W.mul a b) = hcoef ν a * hcoef ν b
  hcoef_one : ∀ (ν : HeckeChi), hcoef ν W.one = 1
  hcoef_abs : ∀ (ν : HeckeChi) (a : W.E), W.Sgood a →
    ‖hcoef ν a‖ = 1
  /-- the Hecke L-function of a finite-order character -/
  Lk : HeckeChi → ℂ → ℂ
  /-- the Dirichlet L-function -/
  Ld : DirChi → ℂ → ℂ
  /-- the quadratic base change: a Dirichlet character viewed as a Hecke
  character through the norm -/
  bc : DirChi → HeckeChi
  /-- the product of two Dirichlet characters -/
  mulChi : DirChi → DirChi → DirChi
  /-- the nontrivial character modulo 3 -/
  chiM3 : DirChi
  m3_nontriv : ¬ IsTrivialD chiM3
  /-- the Euler factors removed by the base change, nonzero on the
  half-plane Re s > 0 -/
  eulerF : DirChi → ℂ → ℂ
  eulerF_nz : ∀ (χ : DirChi) (s : ℂ), 0 < s.re → eulerF χ s ≠ 0
  /-- the base change identity away from s = 1 (section 3 of the source):
  L_K(s, χ ∘ N) = L(s, χ) L(s, χ χ₋₃) up to Euler factors nonzero on
  Re s > 0 -/
  bc_eq : ∀ (χ : DirChi) (s : ℂ), 0 < s.re → s ≠ 1 →
    Lk (bc χ) s = Ld χ s * Ld (mulChi χ chiM3) s * eulerF χ s
  /-- the base change identity at s = 1 -/
  bc_at_one : ∀ (χ : DirChi),
    Lk (bc χ) 1 = Ld χ 1 * Ld (mulChi χ chiM3) 1 * eulerF χ 1
  /-- the base change of χ is trivial exactly when χ is trivial -/
  bc_triv_iff : ∀ (χ : DirChi), IsTrivialH (bc χ) ↔ IsTrivialD χ
  /-- Dirichlet's nonvanishing theorem for χ₋₃: L(1, χ₋₃) ≠ 0 -/
  Ld_M3_one : Ld chiM3 1 ≠ 0
  /-- the Mellin transform of the smoothed Möbius sums, for a Hecke
  character and a weight -/
  Mf : HeckeChi → (ℝ → ℂ) → ℂ → ℂ
  /-- the Mellin transform of the weight -/
  Wf : HeckeChi → (ℝ → ℂ) → ℂ → ℂ
  /-- the Euler-product correction L^S = L · eS -/
  eS : HeckeChi → ℂ → ℂ
  eS_nz : ∀ (ν : HeckeChi) (s : ℂ), 11 / 12 < s.re → eS ν s ≠ 0
  /-- the Mellin transform of a nonnegative compactly supported weight
  is nonzero on the half-plane Re s > 11/12 -/
  Wf_pos : ∀ (ν : HeckeChi) (Wt : ℝ → ℂ) (ρ : ℂ), 11 / 12 < ρ.re →
    Wf ν Wt ρ ≠ 0
  /-- the conditional Mellin identity of section 3: under the power
  saving for the coefficient sequence μ·ν, the Euler product outside S
  inverts the smoothed transform on the half-plane Re s > 11/12. This
  field packages the termwise integration, Hecke's meromorphic
  continuation, and the identity theorem of the source. -/
  mellin_identity : ∀ (ν : HeckeChi) (Wt : ℝ → ℂ),
    MobiusSaving W S (fun n => W.mu n * hcoef ν n) Wt →
      ∀ s : ℂ, 11 / 12 < s.re →
        Lk ν s * Mf ν Wt s * eS ν s = Wf ν Wt s

end QRH


