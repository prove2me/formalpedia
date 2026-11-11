-- Prove2me | Definitions.Def_PermSymQuery_Quadratic_Model
-- name    : PermSymQuery_Quadratic_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:32.687668+00:00
-- url     : https://prove2.me/theorems/8fa5262f-2047-429d-acd1-9bb7bdb03457
-- title:
--   Alphabet query models, signed expectations and local sampling
-- statement:
--   Let $N,b$ be nonnegative integers and let $A$ be a finite alphabet. A string is $x:[N]\to A$. An encoding $\mathrm{enc}:A\to\{0,1\}^b$ supplies the XOR oracle, with an extra address $\bot$ returning the all-zero answer. Permutation invariance requires both $x\circ\pi\in D$ and $f(x\circ\pi)=f(x)$ for every $x\in D$ and position permutation $\pi$. No alphabet-symbol symmetry is required.
--
--   For a promise $D$ and Boolean function $f$ (used only on $D$), the query complexities are the least feasible worst-case budgets:
--   $$Q_\varepsilon(f)=\inf\{T:\exists\text{ quantum algorithm with }T\text{ queries and success }\ge1-\varepsilon\text{ on }D\},$$
--   $$R_\varepsilon(f)=\inf\{d:\exists\text{ randomized decision tree with at most }d\text{ queries and success }\ge1-\varepsilon\text{ on }D\}.$$
--   The infima take values in the extended natural numbers, with empty feasible set giving infinity. For injective encodings and nonnegative error, reading the whole finite input gives finite budgets. Quantum workspaces range over all finite dimensions, and the final output map describes a computational-basis measurement after arbitrary final unitary computation. This represents the paper's arbitrary two-outcome measurements through finite ancillary registers. Classical randomness is a probability mass function over decision trees, with a worst-case bound on every supported tree and input. Nonadaptivity says the complete query list of each supported tree is independent of the input.
--
--   For any quantum algorithm and Boolean output map, $h(x)=\Pr[1]-\Pr[0]$, and $\bar h(x)$ is its uniform average over $x\circ\pi$. A sample $S$ has exactly $s$ labeled positions. A postprocessing rule takes only $S$ and an assignment $z:S\to A$; it is bounded when every such value lies in $[-1,1]$. Its expectation is the sum over samples divided by $\binom Ns$. All theorem uses have $s\le N$; the total definition is zero when $s>N$.
--
--   The parameter layer fixes $K=10^8$, $s(N,T)=\min\{N,K(2T)^2\}$, and
--   $$\eta_{N,s,q}=\frac{60}{\sqrt{N-q}}+\frac{q+1}{N-2q-1}+2\sqrt{\frac2{s-q-1}}.$$
--   A controlled branch vector has amplitudes $a/\sqrt2$ on control zero and $b/\sqrt2$ on control one. These definitions share one query and sampling convention across every target. Empty promises, empty alphabets and $N=0$ remain allowed; the dummy address always exists.
-- source:
--   Yunqi Huang, Lvzhou Li, Zekun Ye, Shenggen Zheng, Optimal Separations Between Randomized and Quantum Query Complexity under Permutation Symmetry, STOC 2027 submission #1644 (October 2026), §§2.1–2.2 and Definition 2.1, PDF pp.7–8 (printed pp.5–6); §3.4 Eq. (7) on PDF p.12 (printed p.10) and Eq. (8) on PDF p.13 (printed p.11); §4 preamble and Lemma 4.1, PDF p.15 (printed p.13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1644.pdf

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QAlgorithms_Defs_Classical

namespace PermSymQuery.Quadratic

open QAlgorithms

/-- §2.1, PDF p.7: the binary answer register, with addition equal to XOR. -/
abbrev Bits (b : ℕ) := Fin b → ZMod 2

/-- The query and workspace basis labels. The address `none` is the dummy address. -/
abbrev StateIndex (N b : ℕ) (W : Type) := ((Option (Fin N) × Bits b) × W)

/-- The encoded input, extended by the zero answer at the dummy address. -/
def encodedInput {N b : ℕ} {A : Type} (enc : A → Bits b) (x : Fin N → A) :
    Option (Fin N) → Bits b := fun i => i.elim 0 (fun j => enc (x j))

/-- §2.1: one symbol query, irrespective of encoding length. -/
def inputOracle {N b : ℕ} {A : Type} (enc : A → Bits b) (x : Fin N → A) :=
  xorOracle (encodedInput enc x)

/-- Definition 2.1, PDF p.8. Only position permutations act; values outside the promise are unused. -/
def PermInvariant {N : ℕ} {A : Type} (D : Set (Fin N → A)) (f : (Fin N → A) → Bool) : Prop :=
  ∀ x ∈ D, ∀ π : Equiv.Perm (Fin N), (x ∘ π) ∈ D ∧ f (x ∘ π) = f x

/-- Realization of the worst-case error with exactly T queries and an arbitrary finite workspace. -/
def QuantumComputes {N b : ℕ} {A : Type} (enc : A → Bits b)
    (D : Set (Fin N → A)) (f : (Fin N → A) → Bool) (ε : ℝ) (T : ℕ) : Prop :=
  ∃ (m : ℕ) (alg : QueryAlg (Option (Fin N)) (Bits b) (Fin m) T)
    (out : StateIndex N b (Fin m) → Bool),
    ∀ x ∈ D, 1 - ε ≤ alg.outputProb (inputOracle enc x) out (f x)

/-- Q_ε of §2.1. An empty feasible set has infimum infinity, never a spurious zero.
For injective encodings and ε ≥ 0, reading all N entries gives a finite feasible query count. -/
noncomputable def Qeps {N b : ℕ} {A : Type} (enc : A → Bits b)
    (D : Set (Fin N → A)) (f : (Fin N → A) → Bool) (ε : ℝ) : ℕ∞ :=
  ⨅ (T : ℕ) (_ : QuantumComputes enc D f ε T), (T : ℕ∞)

/-- Realization of the worst-case error with at most d classical queries. -/
def RandomComputes {N : ℕ} {A : Type} (D : Set (Fin N → A))
    (f : (Fin N → A) → Bool) (ε : ℝ) (d : ℕ) : Prop :=
  ∃ R : RandDecisionTree (Fin N) A Bool,
    RandMakesAtMost R d ∧ ∀ x ∈ D, 1 - ε ≤ successProb R x (f x)

/-- R_ε of §2.1, with worst-case query cost and error. -/
noncomputable def Reps {N : ℕ} {A : Type} (D : Set (Fin N → A))
    (f : (Fin N → A) → Bool) (ε : ℝ) : ℕ∞ :=
  ⨅ (d : ℕ) (_ : RandomComputes D f ε d), (d : ℕ∞)

/-- All addresses seen on the path of an input, including repetitions. -/
def queryList {ι κ α : Type} : DecisionTree ι κ α → (ι → κ) → List ι
  | .leaf _, _ => []
  | .node i next, x => i :: queryList (next (x i)) x

/-- §2.1: internal randomness fixes every query address in advance. -/
def Nonadaptive {N : ℕ} {A : Type} (R : RandDecisionTree (Fin N) A Bool) : Prop :=
  ∀ t ∈ R.support, ∀ x y : Fin N → A, queryList t x = queryList t y

variable {N b T : ℕ} {A W : Type} [Fintype W] [DecidableEq W]

/-- Signed output expectation, §2.1; final measurement is implemented by the output map. -/
noncomputable def signed (enc : A → Bits b)
    (alg : QueryAlg (Option (Fin N)) (Bits b) W T)
    (out : StateIndex N b W → Bool) (x : Fin N → A) : ℝ :=
  alg.outputProb (inputOracle enc x) out true - alg.outputProb (inputOracle enc x) out false

/-- Uniform symmetrization with x^π = x ∘ π, §2.2. -/
noncomputable def symSigned (enc : A → Bits b)
    (alg : QueryAlg (Option (Fin N)) (Bits b) W T)
    (out : StateIndex N b W → Bool) (x : Fin N → A) : ℝ :=
  (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
    ∑ π : Equiv.Perm (Fin N), signed enc alg out (x ∘ π)

/-- Uniform samples of exactly s labeled positions. -/
abbrev Sample (N s : ℕ) := {S : Finset (Fin N) // S.card = s}

/-- A postprocessing rule can see only the values at its own sample's positions. -/
abbrev Postprocess (N s : ℕ) (A : Type) := (S : Sample N s) → (S.val → A) → ℝ

/-- The uniform sample expectation, (9). Used only for s ≤ N; outside that range it is zero. -/
noncomputable def sampleAverage {s : ℕ} (a : Postprocess N s A) (x : Fin N → A) : ℝ :=
  (Nat.choose N s : ℝ)⁻¹ * ∑ S : Sample N s, a S (fun i => x i)

/-- Boundedness is required for every labeled sample and every assignment on it. -/
def BoundedPostprocess {s : ℕ} (a : Postprocess N s A) : Prop :=
  ∀ S z, a S z ∈ Set.Icc (-1 : ℝ) 1

/-- The constants fixed in §3.4 and §4 (PDF pp.13,15). -/
def K : ℕ := 10 ^ 8

def sampleSize (N T : ℕ) : ℕ := min N (K * (2 * T) ^ 2)

/-- η of (7). All subtractions are in ℝ. Lemmas 3.3–3.4 guard the denominators. -/
noncomputable def eta (N s q : ℕ) : ℝ :=
  60 / Real.sqrt ((N : ℝ) - q) + ((q : ℝ) + 1) / ((N : ℝ) - 2 * q - 1) +
    2 * Real.sqrt (2 / ((s : ℝ) - q - 1))

/-- The controlled superposition in Lemma 4.1, before the fixed ancillary embedding. -/
noncomputable def branchState {X : Type} (a b : EuclideanSpace ℂ X) :
    EuclideanSpace ℂ (Bool × X) :=
  WithLp.toLp 2 (fun p => ((Real.sqrt 2)⁻¹ : ℂ) * (if p.1 then b p.2 else a p.2))

end PermSymQuery.Quadratic


