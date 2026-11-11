-- Prove2me | Definitions.Def_CapacitatedKMedianFPT_Main_Leaders
-- name    : CapacitatedKMedianFPT_Main_Leaders
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:14:14.380409+00:00
-- url     : https://prove2.me/theorems/3db38aa6-1992-44ec-811c-b8d4ff5e2fae
-- title:
--   Algorithm 1: sampling masses, ball radii, greedy hitting set, leader candidates and the list L
-- statement:
--   The objects of Algorithm 1 (GuessLeadersAndRadii), for an instance $I$, an error $\varepsilon$ and an uncapacitated solution $(S,\varphi)$.
--
--   1. $Q=\sum_{c\in C}d(c,\varphi(c))$ and the masses $p_c=d(c,\varphi(c))/Q$ (line 3).
--   2. $B_C(f,r)=\{c\in C: d(f,c)\le r\}$ and the radius $r_f=\min\{r\in\mathbb N:\sum_{c\in B_C(f,r)}p_c\ge\varepsilon^2/(12k)\}$ (line 5).
--   3. The set system $\mathcal A=\{B_C(f,r_f): f\in F\}$ (line 6).
--   4. A **greedy hitting set** $H$ of $\mathcal A$: clients chosen one at a time, each hitting the largest number of not yet hit sets, while some set is unhit (line 7).
--   5. Nearest clients $b_s\in\arg\min_{c\in C}d(s,c)$ for $s\in S$ (line 9).
--   6. The **leader candidates** $H\cup\{b_s:s\in S\}$; if $Q=0$, where the masses are undefined, the candidates are $C\cup\{b_s\}$.
--   7. $M=\{\mu_\varepsilon(x):0\le x\le D\}$, $D=\lceil10n^2/\varepsilon\rceil$ (line 10).
--   8. The list $L$ of all pairs $((\ell_1,\dots,\ell_k),(\tilde r_1,\dots,\tilde r_k))$ with every $\ell_i$ a candidate and every $\tilde r_i\in M$ (lines 11–13).
--
--   These are the sets of Claim 1 and Lemma 2.
--
--   **Formalization Note** The tie-breaking of the greedy algorithm and of the minimizers $b_s$ is left open: statements quantify over every greedy run and every choice. When $Q=0$ the radius set is empty and $r_f$ takes Lean's junk value $0$; the candidates do not use it in that case.
-- source:
--   Aditya Anand, Yichen Huang, Ragesh Jaiswal, Amit Kumar, Euiwoong Lee, Jatin Yadav, A Tight FPT Approximation for Capacitated k-Median, STOC 2027 submission #1646 (October 2026), p. 7, Leaders and radii; p. 9, Algorithm 1 (lines 1–14)

import Mathlib
import Definitions.Def_CapacitatedKMedianFPT_Main_Instance

set_option autoImplicit false

/-!
# Algorithm 1 (GuessLeadersAndRadii): the leader candidates `H` and the list `L`

Anand–Huang–Jaiswal–Kumar–Lee–Yadav, STOC 2027 submission #1646, §3, p. 7–9.
-/

namespace CapacitatedKMedianFPT.Main

open scoped BigOperators

noncomputable section

variable {P : Type} [Fintype P] [DecidableEq P]

namespace Instance

variable (I : Instance P)

/-- Line 3: `p_c = d(c, φ(c)) / Q` with `Q = ∑_c d(c, φ(c))`, for the uncapacitated solution
`(S, φ)` of line 2. (Used only when `Q ≠ 0`, see `leaderCandidates`.) -/
def sampleMass (φ : P → P) (c : P) : ℝ := I.d c (φ c) / I.cost φ

/-- `B_C(f, r) = {c ∈ C : d(f, c) ≤ r}` (line 6). -/
def clientBall (f : P) (r : ℝ) : Finset P := I.C.filter (fun c => I.d f c ≤ r)

/-- Line 5: `r_f = min {r ∈ ℕ : ∑_{c ∈ C, d(f,c) ≤ r} p_c ≥ ε²/(12k)}`. The set is nonempty
whenever `Q > 0` (the masses sum to `1 ≥ ε²/(12k)`). -/
def ballRadius (ε : ℝ) (φ : P → P) (f : P) : ℕ :=
  sInf {r : ℕ | ε ^ 2 / (12 * I.k) ≤ ∑ c ∈ I.clientBall f r, I.sampleMass φ c}

/-- Line 6: the set system `A = {B_C(f, r_f) : f ∈ F}`. -/
def ballSystem (ε : ℝ) (φ : P → P) : Finset (Finset P) :=
  I.F.image (fun f => I.clientBall f (I.ballRadius ε φ f))

/-- Line 7: `H` is produced by the greedy hitting-set algorithm on `A` over the clients: it
repeatedly adds a client hitting the largest number of not yet hit sets (any tie-breaking), as long
as some set is unhit. `seq` lists the chosen clients in order. -/
def IsGreedyHittingSet (A : Finset (Finset P)) (H : Finset P) : Prop :=
  ∃ seq : List P, seq.toFinset = H ∧ (∀ B ∈ A, ∃ x ∈ seq, x ∈ B) ∧
    ∀ (t : ℕ) (ht : t < seq.length),
      seq[t] ∈ I.C ∧
      0 < ((A.filter (fun B => ∀ x ∈ seq.take t, x ∉ B)).filter (fun B => seq[t] ∈ B)).card ∧
      ∀ c ∈ I.C,
        ((A.filter (fun B => ∀ x ∈ seq.take t, x ∉ B)).filter (fun B => c ∈ B)).card ≤
          ((A.filter (fun B => ∀ x ∈ seq.take t, x ∉ B)).filter (fun B => seq[t] ∈ B)).card

/-- Line 9: `b_s ∈ argmin_{c ∈ C} d(s, c)` for every `s ∈ S` (any choice of minimizer). -/
def IsNearestClientChoice (S : Finset P) (b : P → P) : Prop :=
  ∀ s ∈ S, b s ∈ I.C ∧ ∀ c ∈ I.C, I.d s (b s) ≤ I.d s c

/-- Lines 7–9: the leader candidates `H ∪ {b_s : s ∈ S}`. When `Q = 0` the masses `p_c` of line 3
are undefined; in that case all clients are taken as candidates (`H := C`). -/
def leaderCandidates (S : Finset P) (φ b : P → P) (H : Finset P) : Finset P :=
  if I.cost φ = 0 then I.C ∪ S.image b else H ∪ S.image b

/-- Line 10: `M = {μ_ε(x) : 0 ≤ x ≤ D}` with `D = ⌈10 n²/ε⌉`. -/
def roundingValues (ε : ℝ) : Finset ℕ :=
  (Finset.range (distanceBound I.size ε + 1)).image (geomRound ε)

/-- Lines 11–13: the list `L` of all pairs of `k` leaders from the candidates and `k` radii from
`M`. -/
def leaderList (ε : ℝ) (S : Finset P) (φ b : P → P) (H : Finset P) :
    Finset ((Fin I.k → P) × (Fin I.k → ℕ)) :=
  Fintype.piFinset (fun _ => I.leaderCandidates S φ b H) ×ˢ
    Fintype.piFinset (fun _ => I.roundingValues ε)

end Instance

end

end CapacitatedKMedianFPT.Main


