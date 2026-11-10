-- Prove2me | Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Sampling
-- name    : QuantumBipartiteTesting_Bipartiteness_Sampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T06:07:49.196376+00:00
-- url     : https://prove2.me/theorems/09a5d498-0d06-478b-b83b-ec1115690997
-- title:
--   Actual block, matching, feasible, and signing distributions
-- statement:
--   Choose each visible label's block independently and uniformly among $\ell$ blocks of capacity $M/\ell$. Overflow means that some capacity is exceeded. Conditional on no overflow, choose a uniform injective placement compatible with the block assignments, and choose independent uniform perfect matchings in every block and color. Perfect matchings are fixed-point-free involutions preserving blocks; their restrictions to visible labels produce the actual graph.
--
--   Finite averages normalize by the cardinality of their sampling set. Invalid or empty sampling sets have default zero; the intended domain has $\ell>0$, $M\ge N$ and $2\ell\mid M$, and the grid theorem establishes validity eventually. YES signs come from independent vertex bits; NO signs come from independent bits on actual distinct edges.
--
--   The integer center and radius are
--   $$M_0=4\lceil11N/40\rceil,\qquad R=\lfloor N^{2/3}/100\rfloor.$$
--   The integer grid requires $1\le\ell\le R$, $|M-M_0|\le R^{3/2}$ and $2\ell\mid M$. The real rectangle has the same inequalities without divisibility.
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), §2.5.1 and §3.1; equation (13), PDF = printed page 11,13,17. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Query

namespace QuantumBipartiteTesting.Bipartiteness
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Normalized finite averaging; the empty finite set has the declared default zero. -/
def Average {T : Type*} (s : Finset T) (f : T → ℝ) : ℝ := (∑ x ∈ s, f x) / s.card

def NoOverflow (N M l : ℕ) (b : Fin N → Fin l) : Prop :=
  ∀ j : Fin l, (univ.filter fun v => b v = j).card ≤ M / l

def OverflowProbability (N M l : ℕ) : ℝ :=
  Average univ fun b : Fin N → Fin l => if NoOverflow N M l b then 0 else 1

def ValidParameters (N M l : ℕ) : Prop := 0 < l ∧ N ≤ M ∧ 2*l ∣ M

def Embeddings {N l : ℕ} (M : ℕ) (b : Fin N → Fin l) : Finset (Fin N → Fin M) :=
  univ.filter fun t => Function.Injective t ∧ ∀ v, (t v).val / (M/l) = (b v).val

/-- Fixed-point-free involutions separately in each canonical ambient block. -/
def Matchings (M l : ℕ) : Finset (Fin M → Fin M) :=
  univ.filter fun h => (∀ v, h (h v) = v ∧ h v ≠ v) ∧
    ∀ v, (h v).val / (M/l) = v.val / (M/l)

def VisibleEdges {N M colors : ℕ} (t : Fin N → Fin M) (h : Fin colors → (Fin M → Fin M)) :
    Finset (ColoredEdge N colors) :=
  univ.filter fun e => e.1 < e.2.1 ∧ h e.2.2 (t e.1) = t e.2.1

/-- Independent uniform matching draws for all colors, written as a finite product law. -/
def MatchingAverage {N M colors : ℕ} (l : ℕ) (t : Fin N → Fin M)
    (f : Finset (ColoredEdge N colors) → ℝ) : ℝ :=
  Average (univ.filter fun h : Fin colors → (Fin M → Fin M) =>
    ∀ j, h j ∈ Matchings M l) fun h => f (VisibleEdges t h)

def FeasibleBase (N M l : ℕ) {colors : ℕ} (f : Finset (ColoredEdge N colors) → ℝ) : ℝ :=
  Average (univ.filter (NoOverflow N M l)) fun b =>
    Average (Embeddings M b) fun t => MatchingAverage l t f

inductive Signing where | yes | no deriving DecidableEq

instance : Fintype Signing := ⟨{.yes, .no}, by intro s; cases s <;> simp⟩

/-- YES uses independent vertex bits, NO independent bits on distinct actual edges. -/
def SigningAverage {N colors : ℕ} (s : Signing) (F : Finset (ColoredEdge N colors))
    (f : (ColoredEdge N colors → Bool) → ℝ) : ℝ :=
  match s with
  | .yes => Average univ fun x : Fin N → Bool => f (fun e => xor (x e.1) (x e.2.1))
  | .no => Average univ fun b : {e // e ∈ F} → Bool =>
      f (fun e => if h : e ∈ F then b ⟨e,h⟩ else false)

def FeasibleAcceptance {N colors k w q : ℕ} (E : Encoding (Fin N × Bool) k)
    (A : Algorithm (Address N colors) k w q)
    (out : (Address N colors × Bits k) × Fin w → Bool) (s : Signing) (M l : ℕ) : ℝ :=
  FeasibleBase N M l fun F => SigningAverage s F fun b =>
    Accept E A out (LiftOracle (SignedResponse F b))

def Center (N : ℕ) : ℕ := 4 * ⌈(11 * N : ℝ) / 40⌉₊
def Radius (N : ℕ) : ℕ := ⌊(N : ℝ) ^ (2/3 : ℝ) / 100⌋₊

def Grid (N M l : ℕ) : Prop :=
  1 ≤ l ∧ l ≤ Radius N ∧ |(M : ℝ) - Center N| ≤ (Radius N : ℝ) ^ (3/2 : ℝ) ∧ 2*l ∣ M

def Rectangle (N : ℕ) (M l : ℝ) : Prop :=
  1 ≤ l ∧ l ≤ Radius N ∧ |M - Center N| ≤ (Radius N : ℝ) ^ (3/2 : ℝ)

end
end QuantumBipartiteTesting.Bipartiteness


