-- Prove2me | Definitions.Def_SingleSampleCombPI_XOS_Algorithms
-- name    : SingleSampleCombPI_XOS_Algorithms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T09:09:23.493168+00:00
-- url     : https://prove2.me/theorems/e7fef50d-f739-4158-b160-1a2635ed8fdd
-- title:
--   Algorithm 4, Algorithm 7 with symmetric tie-breaking, the configuration objective, and the witness of Theorem 6.1
-- statement:
--   1. **Algorithm 4 (buyer-wise greedy).** Prices start at $p=0$. When a buyer arrives, a demand query returns a bundle $S$ maximizing $v(S)-p(S)$, a supporting-price query returns $q_v(\mathbf 1_S)$, the buyer is provisionally allocated $S$, and $p_j\leftarrow q_{v,j}(\mathbf 1_S)$ for $j\in S$ (other prices unchanged). Earlier provisional bundles are never changed. Each step costs one demand query, one supporting-price query and $m+1$ operations.
--   2. **Algorithm 7 with symmetric tie-breaking.** The $2n$ sample and real slots receive uniformly random distinct ranks. Keys are pairs (value, rank) compared lexicographically. The threshold is the largest key among present sampled buyers ($x=1$), or a sentinel below every key if none is present. The algorithm allocates the item to the first present real buyer whose key exceeds the threshold, and to nobody else. Drawing the ranks costs $2n$ operations and each decision $n+(\text{number of earlier arrivals})+2$.
--   3. **Configuration objective (§4.1).** For buyer types $b_1,\dots,b_n$ and a set $I$ of configurations $e_{i,S}=(i,S)$, $p_j(I)=\max_{e_{i,S}\in I,\,S\ni j}q_{i,j}(\mathbf 1_S)$ (empty maximum $0$) and
--   $$f(I)=\sum_{j=1}^m p_j(I).$$
--   For buyer $i$, $U_i(S)=v_i(S)-\sum_{j\in S}p_j(I)$ and $\Delta_i(S)=f(I\cup\{e_{i,S}\})-f(I)$.
--   4. **Witness of Theorem 6.1.** Algorithm 3 with Algorithm 4 as FDAlg, Algorithm 7 as SSPI and $q=1-1/\sqrt3$.
--
--   These are the concrete objects of Theorems 4.1, 5.1 and 6.1 and Lemmas 4.4–4.5; all their properties are theorem obligations.
--
--   **Formalization Note** The printed Algorithm 7 compares values with a strict inequality and takes an empty maximum as $0$; with tied sample and real values it never accepts (see Theorem 5.1). The algorithms call only the oracles $q$ and $d$, never $v$.
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), SHA-256 d6ed330221fdb64a0d8f70c7d0abbd3346ee1cb8f9e101a745f7e1e57d35230e, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/30.pdf, Algorithm 4 (PDF p. 20), Algorithm 7 (PDF p. 29), §4.1 (PDF pp. 21–22), proof of Theorem 6.1 (PDF p. 35)

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Online

open scoped ENNReal

namespace SingleSampleCombPI.XOS

/-! # The concrete algorithms of Theorem 6.1 (Chawla–Dang, STOC 2027 submission #30)

Algorithm 4 (buyer-wise greedy, PDF p. 20), Algorithm 7 (single-sample single-item rule,
PDF p. 29, with symmetric random tie-breaking), the configuration objective of §4.1
(PDF pp. 21–22), and the witness of Theorem 6.1 (PDF p. 35). -/

/-! ## Algorithm 4 -/

/-- One step of Algorithm 4 at prices `p`: ask the demand oracle for a bundle `S` maximizing
`v(S) - p(S)`, ask the supporting-price oracle for `q_v(1_S)`, provisionally allocate `S`,
and set `p_j ← q_{v,j}(1_S)` for `j ∈ S` (other prices unchanged).  Earlier provisional
bundles are never modified. -/
def alg4Step {m : ℕ} (p : Vec m) (b : Buyer m) : AVec .indivisible m × Vec m :=
  let S := b.d p
  let qS := b.q (ind S)
  (⟨ind S, ind_inDom S⟩, fun j => if j ∈ S then qS j else p j)

/-- Algorithm 4 as a (deterministic) online free-disposal algorithm: the state is the price
vector, initially `0`.  Each step makes one demand query, one supporting-price query, and
`m + 1` primitive operations (the price update and the allocation). -/
noncomputable def alg4 (n m : ℕ) : FDAlg .indivisible n m where
  State := Vec m
  Ω := Unit
  seed := RandomSource.ofPMF (PMF.pure ())
  init := fun _ => 0
  step := fun p _ b => alg4Step p b
  seedCost := 0
  stepCost := fun _ _ _ => (m + 1, 1, 1)

/-! ## Algorithm 7 with symmetric tie-breaking -/

/-- Random distinct ranks for the `2n` observable slots: `Sum.inl i` is buyer `i`'s sample
slot and `Sum.inr i` its real slot. -/
abbrev Ranks (n : ℕ) := (Fin n ⊕ Fin n) ≃ Fin (n + n)

instance (n : ℕ) : Nonempty (Ranks n) := ⟨finSumFinEquiv⟩

/-- The comparison key `(value, rank)`, compared lexicographically. -/
def key (it : Item) (r : ℕ) : WithBot (Lex (ℝ × ℕ)) := ((toLex (it.1, r) : Lex (ℝ × ℕ)) : _)

/-- The threshold: the largest key among present samples (`x = 1`), or the sentinel `⊥`
below all keys if no sampled buyer is present. -/
noncomputable def alg7Threshold {n : ℕ} (ω : Ranks n) (s : Fin 1 → Fin n → Item) :
    WithBot (Lex (ℝ × ℕ)) := by
  classical
  exact (Finset.univ.filter (fun i => (s 0 i).2 = 1)).sup (fun i => key (s 0 i) (ω (Sum.inl i)))

/-- A present real arrival beats the threshold. -/
def alg7Beats {n : ℕ} (ω : Ranks n) (τ : WithBot (Lex (ℝ × ℕ))) (i : Fin n) (it : Item) :
    Prop :=
  it.2 = 1 ∧ τ < key it (ω (Sum.inr i))

/-- Algorithm 7 (PDF p. 29), with keys `(q, rank)` under uniformly random distinct ranks of
all `2n` sample and real slots (independent of the Game-of-Googol coins): accept (allocate
`1`) the first present real buyer whose key exceeds the threshold, and nobody else.  Drawing
the ranks costs `2n` operations; a decision recomputes the threshold (`n`), checks the earlier
arrivals and compares its own key. -/
noncomputable def alg7 (n : ℕ) : KSPI .indivisible n 1 where
  Ω := Ranks n
  seed := RandomSource.ofPMF (PMF.uniformOfFintype (Ranks n))
  act := fun ω s hist i it => by
    classical
    exact if (∀ e ∈ hist, ¬ alg7Beats ω (alg7Threshold ω s) e.1 e.2) ∧
        alg7Beats ω (alg7Threshold ω s) i it then 1 else 0
  seedCost := 2 * n
  actCost := fun _ _ hist _ _ => n + hist.length + 2

/-! ## Configuration objective of §4.1 -/

/-- The configuration ground set `N = {e_{i,S} : i ∈ [n], S ⊆ [m]}`; the part of buyer `i`
is `{(i, S) : S ⊆ [m]}`. -/
abbrev Config (n m : ℕ) := Fin n × Finset (Fin m)

/-- `p_j(I) = max_{e_{i,S} ∈ I, S ∋ j} q_{i,j}(S)` (empty maximum `0`). -/
noncomputable def priceOf {n m : ℕ} (b : Fin n → Buyer m) (I : Finset (Config n m))
    (j : Fin m) : ℝ := by
  classical
  exact maxOrZero (I.filter (fun e => j ∈ e.2)) (fun e => (b e.1).q (ind e.2) j)

/-- The configuration objective `f(I) = ∑_j p_j(I)`, defined on all configuration sets. -/
noncomputable def configObj {n m : ℕ} (b : Fin n → Buyer m) (I : Finset (Config n m)) : ℝ :=
  ∑ j, priceOf b I j

/-- Buyer-wise utility `U_i(S) = v_i(S) - p(S)` at the prices `p_j = p_j(I)`. -/
noncomputable def utilU {n m : ℕ} (b : Fin n → Buyer m) (I : Finset (Config n m)) (i : Fin n)
    (S : Finset (Fin m)) : ℝ :=
  (b i).v (ind S) - ∑ j ∈ S, priceOf b I j

/-- Marginal contribution `Δ_i(S) = f(I ∪ {e_{i,S}}) - f(I)`. -/
noncomputable def margΔ {n m : ℕ} (b : Fin n → Buyer m) (I : Finset (Config n m)) (i : Fin n)
    (S : Finset (Fin m)) : ℝ :=
  configObj b (insert (i, S) I) - configObj b I

/-! ## The witness of Theorem 6.1 -/

/-- The role probability `q = 1 - 1/√3`. -/
noncomputable def qStar : ℝ := 1 - 1 / Real.sqrt 3

/-- The allocation of the witness: Algorithm 3 with Algorithm 4 as FDAlg and Algorithm 7 as
SSPI. -/
noncomputable def witnessOut (n m : ℕ) (H : Fin n → Bool) (π : Equiv.Perm (Fin n))
    (ωs : Fin m → Ranks n) (ρ : Equiv.Perm (Fin n)) (s' r' : Fin n → Buyer m) :
    Fin n → Vec m :=
  alg3 (alg4 n m) (alg7 n) H π () ωs ρ s' r'

end SingleSampleCombPI.XOS


