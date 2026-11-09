-- Prove2me | Definitions.Def_SwitchingRegret_Dyadic_Model
-- name    : SwitchingRegret_Dyadic_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:25:32.900993+00:00
-- url     : https://prove2.me/theorems/a21f8d66-1bf9-4bbf-ab82-367b94cc5d9b
-- title:
--   Finite bandit model, dyadic intervals, entropy updates and product seeds
-- statement:
--   Arms are the $K$ coordinates of a real vector. The simplex has nonnegative coordinates summing to one, and $X$ has nonnegative coordinates summing to at most one. Completion adds a reference coordinate of mass $1-\sum_i x_i$. Relative entropy against a strictly positive vector uses $0\log0=0$.
--
--   For a horizon $T$, a loss table has entries in $[0,1]$ on rounds $1,\ldots,T$, and a comparator is an arm sequence; its switch count counts consecutive unequal arms starting at round 2. The constants are
--   $$L=\lceil8\log T\rceil,\quad \alpha=L^{-2},\quad \eta_j=2^{j-1}L/\sqrt{KT}.$$
--   Canonical intervals are $\{k2^h+1,\ldots,(k+1)2^h\}$ with endpoint at most $T$. The maximal comparator-constant intervals contained in a prefix define its cover.
--
--   The finite product seed law gives independent uniform variables on $(0,1)$ for routing, main actions, challenge actions and interval rates, for every epoch. A routing uniform below $1/2$ gives a main round. Inverse CDF sampling and the two normalized exponential updates are explicit functions. These are the shared model primitives, with no regret assumptions.
--
--   **Formalization Note** Arms use zero-based labels; rounds and epochs retain the source's positive labels. Extra unused seed coordinates at index 0 and noncanonical grid locations have no effect. All uses of real-valued finite KL are against the full-support prior, never against a vector with a zero denominator.
-- source:
--   Mengxiao Zhang, Toward Optimal Switching Regret for Multi-Armed Bandits with Oblivious Adversary, 2026 preprint, STOC 2027 submission #99, SHA-256 70dc03d632eeb5878823d984fc755157b34301d8189bbd7a6087570a8f8a7fee, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/99.pdf, Section 2, Eq. (4), Appendix A.1, PDF pp. 4, 7, 17–18 (printed pp. 3, 6, 16–17); closed forms PDF pp. 20, 25

import Mathlib

noncomputable section

namespace SwitchingRegret.Dyadic
open Classical MeasureTheory

/-- Section 2, PDF 4: finite arm vectors, with zero-based arm labels. -/
abbrev Vec (K : ℕ) := Fin K → ℝ

def simplex {K : ℕ} (x : Vec K) : Prop := (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1

def subSimplex {K : ℕ} (x : Vec K) : Prop := (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1

def dot {K : ℕ} (x y : Vec K) : ℝ := ∑ i, x i * y i

def mass {K : ℕ} (x : Vec K) : ℝ := ∑ i, x i

def complete {K : ℕ} (x : Vec K) : Option (Fin K) → ℝ
  | none => 1 - mass x
  | some i => x i

/-- Used only against the strictly positive initial law in Lemma A.1. The zero
coordinate contributes zero, as in the paper's 0 log 0 convention. -/
def finiteKL {ι : Type*} [Fintype ι] (x y : ι → ℝ) : ℝ :=
  ∑ i, if x i = 0 then 0 else x i * Real.log (x i / y i)

def L (T : ℕ) : ℕ := ⌈8 * Real.log T⌉₊
def alpha (T : ℕ) : ℝ := 1 / (L T : ℝ) ^ 2
def eta (K T j : ℕ) : ℝ := (2 : ℝ) ^ (j - 1) * (L T : ℝ) / Real.sqrt (K * T : ℕ)
def initialX (K T : ℕ) : Vec K := fun _ => 1 / ((K : ℝ) * (T + 1))
def prior (K T : ℕ) : Option (Fin K) → ℝ
  | none => (T : ℝ) / (T + 1)
  | some _ => 1 / ((K : ℝ) * (T + 1))

/-- Loss rows outside 1,...,T are ignored everywhere. -/
abbrev LossTable (K : ℕ) := ℕ → Vec K

def validLoss {K : ℕ} (T : ℕ) (ell : LossTable K) : Prop :=
  ∀ t ∈ Finset.Icc 1 T, ∀ i, ell t i ∈ Set.Icc (0 : ℝ) 1

def switches {K : ℕ} (T : ℕ) (u : ℕ → Fin K) : ℕ :=
  ((Finset.Icc 2 T).filter fun t => u t ≠ u (t - 1)).card

/-- A finite ambient grid; the filter `dyadics` is the canonical family (4).
For 2^h ≤ T every possible exponent satisfies h ≤ T. -/
abbrev Dyad (T : ℕ) := Fin (T + 1) × Fin (T + 1)
def first {T : ℕ} (J : Dyad T) : ℕ := J.1.val * 2 ^ J.2.val + 1
def last {T : ℕ} (J : Dyad T) : ℕ := (J.1.val + 1) * 2 ^ J.2.val
def rounds {T : ℕ} (J : Dyad T) : Finset ℕ := Finset.Icc (first J) (last J)
def dyadics (T : ℕ) : Finset (Dyad T) := Finset.univ.filter fun J => last J ≤ T
def future (T tau : ℕ) : Finset (Dyad T) := (dyadics T).filter fun J => tau ≤ first J

def constantOn {K : ℕ} (u : ℕ → Fin K) {T : ℕ} (J : Dyad T) : Prop :=
  ∀ t ∈ rounds J, u t = u (first J)

def cover {K : ℕ} (T tau n : ℕ) (u : ℕ → Fin K) : Finset (Dyad T) :=
  let candidates := (future T tau).filter fun J => last J ≤ n ∧ constantOn u J
  candidates.filter fun J => ∀ J' ∈ candidates, rounds J ⊆ rounds J' → rounds J' ⊆ rounds J

/-- Concrete finite product of the three round seed families and interval rates.
A fair routing bit is the threshold of its independent uniform coordinate. -/
abbrev SeedKey (T : ℕ) := Fin (T + 1) ⊕ (Fin (T + 1) ⊕ (Fin (T + 1) ⊕ Dyad T))
abbrev EpochSeed (T : ℕ) := SeedKey T → ℝ
abbrev RunSeed (T : ℕ) := Fin (T + 1) → EpochSeed T
abbrev ChallengeSeed (T : ℕ) := Fin (T + 1) → ℝ

def uniform01 : Measure ℝ := volume.restrict (Set.Ioo 0 1)
def epochLaw (T : ℕ) : Measure (EpochSeed T) := Measure.pi fun _ => uniform01
def runLaw (T : ℕ) : Measure (RunSeed T) := Measure.pi fun _ => epochLaw T
def challengeLaw (T : ℕ) : Measure (ChallengeSeed T) := Measure.pi fun _ => uniform01

def timeKey (T t : ℕ) : Fin (T + 1) := ⟨t % (T + 1), Nat.mod_lt _ (by omega)⟩
def mainRound {T : ℕ} (xi : EpochSeed T) (t : ℕ) : Bool :=
  decide (xi (.inl (timeKey T t)) < 1 / 2)
def mainSeed {T : ℕ} (xi : EpochSeed T) (t : ℕ) : ℝ := xi (.inr (.inl (timeKey T t)))
def chalSeed {T : ℕ} (xi : EpochSeed T) (t : ℕ) : ℝ := xi (.inr (.inr (.inl (timeKey T t))))
def rateSeed {T : ℕ} (xi : EpochSeed T) (J : Dyad T) : ℝ := xi (.inr (.inr (.inr J)))
def intervalRate (K T j : ℕ) (xi : EpochSeed T) (J : Dyad T) : ℝ :=
  alpha T * eta K T j / rateSeed xi J

/-- The non-challenge coordinates fixed when conditioning on F^rate. -/
structure FixedSeeds (T : ℕ) where
  routing : Fin (T + 1) → Bool
  main : Fin (T + 1) → ℝ
  rates : Dyad T → ℝ

def FixedSeeds.valid {T : ℕ} (f : FixedSeeds T) : Prop :=
  (∀ t, f.main t ∈ Set.Ioo (0 : ℝ) 1) ∧ (∀ J, f.rates J ∈ Set.Ioo (0 : ℝ) 1)

def assemble {T : ℕ} (f : FixedSeeds T) (v : ChallengeSeed T) : EpochSeed T
  | .inl t => if f.routing t then 1 / 4 else 3 / 4
  | .inr (.inl t) => f.main t
  | .inr (.inr (.inl t)) => v t
  | .inr (.inr (.inr J)) => f.rates J

/-- Appendix A.1 inverse CDF, with an arbitrary default off the simplex or when
u is outside (0,1). The default is never needed in the stated probabilistic model. -/
def sample {K : ℕ} [NeZero K] (p : Vec K) (u : ℝ) : Fin K :=
  let candidates := Finset.univ.filter fun a : Fin K => u ≤ ∑ k ∈ Finset.Iic a, p k
  if h : candidates.Nonempty then candidates.min' h
  else ⟨0, Nat.pos_of_ne_zero (NeZero.ne K)⟩

/-- The two entropy OMD closed forms, PDF 20 and 25. -/
def expUpdate {ι : Type*} [Fintype ι] (x y : ι → ℝ) (r : ℝ) : ι → ℝ :=
  fun i => x i * Real.exp (-r * y i) / ∑ k, x k * Real.exp (-r * y k)

def mainUpdate {K : ℕ} (T : ℕ) (q loss : Vec K) (r : ℝ) : Vec K :=
  fun i => (1 - 1 / (T : ℝ)) * expUpdate q loss r i + 1 / ((K : ℝ) * T)

def intervalUpdate {K : ℕ} (x q loss : Vec K) (r : ℝ) : Vec K :=
  let y : Option (Fin K) → ℝ := fun a => match a with
    | none => dot q loss
    | some i => loss i
  fun i => expUpdate (complete x) y r (some i)

end SwitchingRegret.Dyadic


