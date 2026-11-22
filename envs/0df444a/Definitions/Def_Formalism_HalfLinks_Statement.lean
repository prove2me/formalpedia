-- Prove2me | Definitions.Def_Formalism_HalfLinks_Statement
-- name    : Formalism_HalfLinks_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:24:06.718495+00:00
-- url     : https://prove2.me/theorems/4563cbbf-b641-413c-8359-495c35e301a4
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HalfLinks/Statement.lean

import Definitions.Def_Formalism_ZetaNonvanishingChebyshevWeights
import Definitions.Def_Formalism_StatementCM
import Definitions.Def_Formalism_ProductFormula_StatementOCCM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
namespace Formalism.CMTypeGaloisData
open Formalism
abbrev Gal3 := Fin 3 → ℤˣ
def cc : Gal3 := fun _ => -1
def IsCMType3 (Φ : Finset Gal3) : Prop := 1 ∈ Φ ∧ ∀ s : Gal3, s ∈ Φ ↔ cc * s ∉ Φ
def oppType (Φ : Finset Gal3) : Finset Gal3 := insert 1 ((Φ.erase 1).image (fun s => cc * s))
def oddSet : Fin 4 → Finset (Fin 3) := ![{0}, {1}, {2}, Finset.univ]
def oddChar (i : Fin 4) (g : Gal3) : ℤ := ∏ j ∈ oddSet i, ((g j : ℤˣ) : ℤ)
def frob (chi : Fin 4 → ℕ → ℝ) (n : ℕ) : Gal3 := fun i => if chi (Fin.castSucc i) n = -1 then -1 else 1
def Unram (chi : Fin 4 → ℕ → ℝ) (X : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X → Λ n ≠ 0 →
    (∀ i : Fin 3, chi (Fin.castSucc i) n = 1 ∨ chi (Fin.castSucc i) n = -1) ∧
      chi 3 n = chi 0 n * chi 1 n * chi 2 n
def AT (chi : Fin 4 → ℕ → ℝ) (Ψ : Finset Gal3) (y : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊y⌋₊, if frob chi n ∉ Ψ then Λ n * (y / n - 1) else 0
def Schi4 (χ : ℕ → ℝ) (y : ℝ) : ℝ := ∑ n ∈ Icc 1 ⌊y⌋₊, Λ n * χ n * (y / n - 1)
def Gch (χ : ℕ → ℝ) (ell y : ℝ) : ℝ := Schi4 χ y + y * ell
def tp (x ε B : ℝ) (k : ℕ) (r : ℕ → ℕ) (p : ℕ) : ℝ :=
  x * B / (p : ℝ) ^ (2 * r p) + x ^ ε * (k + x * B / (p * k))
def classC (x ε B : ℝ) (m k : ℕ) (Pc : Finset ℕ) (κ : ℕ → ℝ) (r : ℕ → ℕ) (y0 : ℝ) : ℝ :=
  (∑ p ∈ Pc, Real.log p * (tp x ε B k r p / B + x ^ ε * m * κ p * x / p))
    + (∑ p ∈ Pc.filter (fun p : ℕ => (p : ℝ) ≤ y0), (r p : ℝ) * Real.log p)
structure HrData (θ ε x X : ℝ) (m : ℕ) where

  Pc : Finset ℕ
  κ : ℕ → ℝ
  r : ℕ → ℕ
  Pc_prime : ∀ p ∈ Pc, p.Prime
  Pc_le : ∀ p ∈ Pc, (p : ℝ) ≤ X
  κ_nonneg : ∀ p ∈ Pc, 0 ≤ κ p
  κ_sum : (∑ p ∈ Pc, κ p * Real.log p / p) ≤ x ^ (θ - 1 - ε) / m
  r_pos : ∀ p ∈ Pc, 1 ≤ r p
  r_le : ∀ p ∈ Pc, (r p : ℝ) ≤ x ^ ε
  r_small : ∀ p ∈ Pc, (p : ℝ) ≤ x ^ (1 - θ) → x ^ (1 - θ) * x ^ (1 - θ) ≤ (p : ℝ) ^ (2 * r p)
  r_large : ∀ p ∈ Pc, x ^ (1 - θ) < p → r p = 1
def ATg {G : Type} [DecidableEq G] (frob : ℕ → G) (Bad : Finset ℕ) (Ψ : Finset G) (y : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊y⌋₊, if n.minFac ∉ Bad ∧ frob n ∉ Ψ then Λ n * (y / n - 1) else 0
structure HostSizeData (G : Type) [CommGroup G] [Fintype G] [DecidableEq G] (X : ℝ) where
  c : G
  c_ne : c ≠ 1
  c_sq : c * c = 1
  nT : ℕ
  types : Fin nT → Finset G
  cm : ∀ t s, s ∈ types t ↔ c * s ∉ types t
  w : Fin nT → ℝ
  w_nonneg : ∀ t, 0 ≤ w t
  w_sum : (∑ t, w t) = 2
  chars : Finset (G →* ℂˣ)
  odd : ∀ ψ ∈ chars, ψ c = -1
  coef : (G →* ℂˣ) → ℝ
  decomp : ∀ s : G, (∑ t, w t * (if s ∉ types t then (1 : ℝ) else 0))
    = 1 - (∑ ψ ∈ chars, coef ψ * ((ψ s : ℂˣ) : ℂ).re)
  Bad : Finset ℕ
  frob : ℕ → G
  chi : (G →* ℂˣ) → ℕ → ℝ
  unram : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X → Λ n ≠ 0 → ∀ ψ ∈ chars,
    chi ψ n = if n.minFac ∈ Bad then 0 else ((ψ (frob n) : ℂˣ) : ℂ).re
structure HalfLinksCore (G : Type) [CommGroup G] [Fintype G] [DecidableEq G] (C ε θ x B D : ℝ)
    (m k f : ℕ) where
  host : HostSizeData G (4 * x * (m : ℝ) ^ 2)

  ell : (G →* ℂˣ) → ℝ

  ramP : Finset ℕ
  ram_ge : ∀ q ∈ ramP, D ≤ q
  ram_card : (ramP.card : ℝ) ≤ Real.log D

  L0 : ℝ
  initialLengthNonneg : 0 ≤ L0
  initialLengthLe : L0 ≤ 2 * (k + 2 * m) * f * B
  top : Fin m → ℝ
  low : Fin m → ℝ
  cls : Fin m → ℝ
  ram : Fin m → ℝ

  lift : ∀ j : Fin m,
    B * chebNode m j * (∑ t, host.w t * ATg host.frob host.Bad (host.types t) (x / chebNode m j))
      ≤ x * B * (Real.log (x / chebNode m j) - 1 - Real.eulerMascheroniConstant
          + (∑ ψ ∈ host.chars, host.coef ψ * ell ψ))
        + (top j + low j + cls j + ram j)

  top_le : (∑ j, top j) ≤ C * x ^ ε * (m * B) * (x / m + x * m / k)

  div : ∀ j, low j ≤ C * x ^ ε * f * m * B

  hr : HrData θ ε x (4 * x * (m : ℝ) ^ 2) m

  cls_le : (∑ j, cls j) ≤ C * x ^ ε * (m * B) * classC x ε B m k hr.Pc hr.κ hr.r (x ^ (1 - θ))

  ram_le : ∀ j, ram j ≤ ∑ q ∈ ramP, C * (x * B + L0) * Real.log q / ((q : ℝ) - 1)
structure HalfLinks (G : Type) [CommGroup G] [Fintype G] [DecidableEq G] (C ε θ x B D : ℝ)
    (m k f : ℕ) extends HalfLinksCore G C ε θ x B D m k f where

  landau : (∑ ψ ∈ host.chars, host.coef ψ * chebyshevWeightedAverage m x (Gch (host.chi ψ) (ell ψ)))
    ≤ C * Real.sqrt (x * Real.log x) * Real.log D ^ 2
def HalfSize (θ ε K x B D : ℝ) (m k f : ℕ) : Prop :=
  0 < m ∧ 0 < k ∧ 0 < B ∧ x ^ (1 - θ) ≤ m ∧ (m : ℝ) ≤ x ∧ x * m ≤ K * x ^ θ * k ∧ (k : ℝ) ≤ x ^ 2 ∧
    (f : ℝ) * m ≤ K * x ^ (θ + ε) ∧ (f : ℝ) ≤ x ∧ x ^ 4 * k ≤ B ∧ x ^ 4 ≤ D ∧ Real.log D ≤ x ^ ε
def HalfCore : Prop :=
  ∀ θ ε C K : ℝ, 1 / 2 ≤ θ → θ < 1 → 0 < ε → 1 ≤ C → ∃ K' x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x →
    ∀ (G : Type) [CommGroup G] [Fintype G] [DecidableEq G] (m k f : ℕ) (B D : ℝ),
      HalfSize θ ε K x B D m k f → ∀ H : HalfLinksCore G C ε θ x B D m k f,
      2 * x * (∑ p ∈ H.host.Bad.filter Nat.Prime, Real.log p / p) ≤ K * x ^ (θ + ε) →
      chebyshevWeightedAverage m x Gz - (∑ ψ ∈ H.host.chars, H.host.coef ψ * chebyshevWeightedAverage m x (Gch (H.host.chi ψ) (H.ell ψ)))
        ≤ K' * x ^ (θ + 3 * ε)
def HalfToZeta : Prop :=
  ∀ θ : ℝ, 1 / 2 ≤ θ → θ < 1 →
  (∀ ε : ℝ, 0 < ε → ∃ C K x₀ : ℝ, 1 ≤ C ∧ ∀ x : ℝ, x₀ ≤ x →
    ∃ (G : Type) (_ : CommGroup G) (_ : Fintype G) (_ : DecidableEq G) (m k f : ℕ) (B D : ℝ),
      HalfSize θ ε K x B D m k f ∧ ∃ H : HalfLinks G C ε θ x B D m k f,
        2 * x * (∑ p ∈ H.host.Bad.filter Nat.Prime, Real.log p / p) ≤ K * x ^ (θ + ε)) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0
def RiemannHypothesisOfHalfLinks : Prop :=
  (∀ ε : ℝ, 0 < ε → ∃ C K x₀ : ℝ, 1 ≤ C ∧ ∀ x : ℝ, x₀ ≤ x →
    ∃ (G : Type) (_ : CommGroup G) (_ : Fintype G) (_ : DecidableEq G) (m k f : ℕ) (B D : ℝ),
      HalfSize (1 / 2) ε K x B D m k f ∧ ∃ H : HalfLinks G C ε (1 / 2) x B D m k f,
        2 * x * (∑ p ∈ H.host.Bad.filter Nat.Prime, Real.log p / p) ≤ K * x ^ ((1 : ℝ) / 2 + ε)) →
  RiemannHypothesis
def HalfWindowAt (C ε x : ℝ) (m k f k0 : ℕ) (b t NA η D : ℝ) : Prop :=
  C * (m : ℝ) ^ 2 ≤ k ∧
  Real.log b ≤ x ^ ε ∧
  k * (4 * x * (m : ℝ) ^ 2) / m ≤ b ∧
  x ^ C ≤ b ∧
  k * (k0 * NA) ≤ m * b ∧
  0 < NA ∧ t = b / NA ∧ (k : ℝ) ≤ t ∧
  t ^ 2 * f * Real.log t ≤ m * b * x ^ ε ∧
  C * m * k * t ≤ η ∧
  2 * m * t ≤ η ∧
  t * η ≤ b ∧
  k * k0 * NA / m ≤ b ∧ b ≤ NA ^ 2 / (m * k) ∧
  (k : ℝ) ^ 2 * k0 ≤ NA ∧
  η * t * (k : ℝ) ^ C ≤ b ∧
  (k : ℝ) ^ C * Real.sqrt b ≤ η ∧
  x ^ (40 : ℝ) ≤ D ∧ Real.log D ≤ x ^ ε ∧ 4 * x * (m : ℝ) ^ 2 < D ∧
  (8 * D ^ 3) ^ C ≤ b ∧ D ^ C ≤ b
def HalfWindow : Prop :=
  ∀ C ε : ℝ, 1 ≤ C → 0 < ε → ε < 1 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ f : ℕ, (f = 4 ∨ f = ⌈x ^ ε⌉₊) →
    ∃ (k0 : ℕ) (b t NA η : ℝ), 1 ≤ k0 ∧ Real.log b = Real.log x ^ 3 ∧
      HalfWindowAt C ε x ⌈x ^ (1 / 2 : ℝ)⌉₊ ⌈x ^ (1 + ε)⌉₊ f k0 b t NA η (x ^ (40 : ℝ)) ∧
      HalfSize (1 / 2) ε 8 x b (x ^ (40 : ℝ)) ⌈x ^ (1 / 2 : ℝ)⌉₊ ⌈x ^ (1 + ε)⌉₊ f
def Conflict1 : Prop :=
  ∀ (m : ℕ) (B t η : ℝ), 2 ≤ m → 0 < B → 2 ≤ t → t * η ≤ B →
    ∃ i j : Fin m, η < B * chebNode m i - B * chebNode m j
def Conflict2 : Prop :=
  ∀ ε c0 : ℝ, 0 < ε → 0 < c0 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (m k b : ℕ) (t : ℝ),
    (m : ℝ) ≤ 2 * x ^ (1 / 2 : ℝ) → x ^ (1 + ε) ≤ k → (k : ℝ) ≤ t → 1 ≤ b →
    ∃ l : ℕ, l.Prime ∧ b < l ∧ l ≤ 2 * b ∧ (b : ℝ) * m / t < l ∧
      c0 * m * x ^ ε * (1 + (b : ℝ) / l) < t
end Formalism.CMTypeGaloisData


