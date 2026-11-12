-- Prove2me | Definitions.Def_RelatedSchedFPTAS796_Main_Algorithm1
-- name    : RelatedSchedFPTAS796_Main_Algorithm1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:12:57.280293+00:00
-- url     : https://prove2.me/theorems/822eefef-cf96-41fb-92db-6dc91100f51b
-- title:
--   Algorithm 1 (Randomly Partition) as a distribution over its exact set expression
-- statement:
--   Fix accuracy $\varepsilon=2^{-\ell}$, a partial-profile instance $(J,\kappa,q)$ of dimension $d$ and a **complete-profile procedure** $\mathrm{CP}$, which on an accuracy, a number $k$ of machines, a multiset $B$ of jobs, targets $t\in\mathbb Q^k$ and a failure parameter $q_0$ returns a random finite subset of $\mathbb Q^k$; its known coordinatewise error bound is $C_1\varepsilon t_i(\log_2(|B|+2)\log_2(2/\varepsilon)\log_2(2/q_0))^{c_1}$. Algorithm 1 (pp.10–11) is transcribed line by line:
--
--   1. $d'$ is the smallest index in $\{1,\dots,d-1\}$ with $6\frac{2d+1}{2d}\kappa_{d'}\log\big(\frac{3d}{q}\frac{2d+1}{2d}\kappa_{d'}\big)<\kappa_{d'+1}$, and $d'=d$ if there is none; $K=\lceil\frac{2d+1}{2d}\kappa_{d'}\rceil$, $R=\lceil\log_{4/3}(3K/q)\rceil$, $\gamma=6d\log(3dK/q)$, $G$ the least power of two at least $\lceil\gamma\rceil^2$, $q_0=q/(3R(KG+|J|))$, and $u_i=(4d+2)\kappa_i/(dK\varepsilon)$ for $i>d'$.
--   2. $J$ is partitioned independently and uniformly into $J_1,\dots,J_K$; for each repetition $r=1,\dots,R$ every $J_\ell$ is partitioned independently and uniformly into $J^{(r)}_{\ell,1},\dots,J^{(r)}_{\ell,G}$.
--   3. For $B=J^{(r)}_{\ell,g}$: if $d'=d$ the leaf is $\{0\}\cup\{ae_i: a\in\mathrm{supp}(B),1\le i\le d\}$. Otherwise $\tilde T\leftarrow\mathrm{CP}(B,(u,\Sigma(B)),q_0)$, $S_0=\{0_{d'}\}\times\pi(\tilde T)$, and for every $a\in\mathrm{supp}(B)$, $\tilde T_a\leftarrow\mathrm{CP}(B\setminus\{a\},(u,\Sigma(B)-a),q_0)$ and $S_a=\bigcup_{i=1}^{d'}\{ae_i\}\times\pi(\tilde T_a)$; the leaf is $S_0\cup\bigcup_aS_a$. Here $\pi$ discards the implicit (last) coordinate, keeps the points whose explicit coordinates are at most $u_i$ plus the call's error bound, and caps each coordinate at $u_i$; an empty recursive job set is handled directly by its profile set $\{0\}$. Finally the leaf $S^{(r)}_{\ell,g}$ receives $0_d$ and all axis projections $x_je_j$ of its points.
--   4. The output is the exact set expression
--   $$S=S_1+\dots+S_K,\qquad S_\ell=\bigcup_{r=1}^{R}\big(S^{(r)}_{\ell,1}+\dots+S^{(r)}_{\ell,G}\big).$$
--
--   All partitions and calls use independent randomness, so the algorithm defines a probability distribution over the set $S$. This is the object of Lemma 4.4.
--
--   **Formalization Note** Parts are numbered from $0$; $\kappa$ is indexed from $0$ in Lean and read with the paper's $1$-based index through `kap`. The sumset procedure of lines 22–24 is replaced by the exact set expressions, as in the statement of Lemma 4.4.
-- source:
--   Lin Chen, Tingwei Hu, Jiayi Lian, Yuchen Mao, Guochuan Zhang, Faster Approximation Schemes for Scheduling on Related Machines, STOC 2027 submission #796 (October 2026), source.pdf SHA-256 5d7d0135eed9cbe942c80598e2bb07d8c56ab67aec0d6e8486a067237654f7f3, §4.2 pp.10–11, the parameters d′, K, R, u, π (p.10 line 390 – p.11 line 402) and Algorithm 1 (p.11, lines 1–21); Lemma 4.4 p.12

import Mathlib
import Definitions.Def_RelatedSchedFPTAS796_Main_Model
import Definitions.Def_RelatedSchedFPTAS796_Main_Machine

set_option autoImplicit false

namespace RelatedSchedFPTAS796.Main

/-!
# Algorithm 1 (Randomly Partition) as a probability distribution over its exact set expression

Chen, Hu, Lian, Mao, Zhang, *Faster Approximation Schemes for Scheduling on Related Machines*,
STOC 2027 submission #796 (October 2026), §4.2 pp.10–11: the parameters `d'`, `K`, `R`, `u`, `π`
(p.10 line 390 – p.11 line 402) and Algorithm 1 (p.11, lines 1–21), with the exact set expressions
`S_ℓ = ⋃_{r=1}^{R} (S^{(r)}_{ℓ,1} + ⋯ + S^{(r)}_{ℓ,G})` and `S = S_1 + ⋯ + S_K` of Lemma 4.4 (p.12)
in place of the sumset procedure of lines 22–24.

**Formalization Note.**
* The instance is `(J, κ, q)` with `ε = 2^{−ℓ}`; `J` is a list of job sizes (occurrences
  `0, …, |J| − 1`), `κ : Fin d → ℚ` with `κ_i` the paper's `κ_{i+1}`.
* `CompleteProfile` is a parameter `cp`: for the accuracy `ε = 2^{−ℓ}` (the same as the
  instance's), a number `k` of machines, a multiset `B` of jobs,
  targets `t ∈ ℚ^k` and a failure parameter `q₀` it returns a distribution over finite sets of
  `ℚ^k`. Its "known coordinatewise additive error bound" (p.11 line 399) is
  `C₁·ε·t_i·(log₂(|B|+2)·log₂(2/ε)·log₂(2/q₀))^{c₁}` (`cpError`), the form of Definition 3.1.
  The recursive targets are `(u, Σ(B))` with the implicit machine last; `π` discards the last
  coordinate, keeps the points whose remaining coordinates are at most `u_i` plus the error bound,
  and caps each coordinate at `u_i`. An empty recursive job set is handled directly by its exact
  profile set `{0}` (p.11 line 401).
* Random partitions put every job occurrence independently and uniformly into one of the parts
  (`randomPartition`, parts numbered `0, …, K − 1`); the `R` second-layer partitions of every
  `J_ℓ` (line 8) are one independent uniform labelling of all occurrences per repetition. All
  recursive calls draw independent randomness.
* The output is the exact set `S = ∑_{ℓ<K} ⋃_{r<R} ∑_{g<G} S^{(r)}_{ℓ,g} ⊆ ℚ^d`.
-/

open Pointwise

/-- A complete-profile procedure: accuracy `ε = 2^{−ℓ}`, number of machines, jobs, targets, failure
parameter ↦ a distribution over finite output sets. -/
abbrev CPProcedure := (ℓ k : ℕ) → Multiset ℕ → (Fin k → ℚ) → ℚ → PMF (Finset (Fin k → ℚ))

/-- The known coordinatewise error bound of a call: `C₁·ε·t_i·polylog^{c₁}` with
`polylog = log₂(|B|+2)·log₂(2/ε)·log₂(2/q₀)`, `ε = 2^{−ℓ}`. -/
noncomputable def cpError (ℓ C₁ c₁ : ℕ) {k : ℕ} (B : Multiset ℕ) (t : Fin k → ℚ) (q₀ : ℚ)
    (i : Fin k) : ℝ :=
  C₁ * epsOf ℓ * (t i : ℝ) * polylog3 B.card (epsOf ℓ) q₀ c₁

variable {d : ℕ}

/-- `κ_i` with the paper's `1`-based index (`0` outside `1, …, d`). -/
def kap (κ : Fin d → ℚ) (i : ℕ) : ℚ := if h : i - 1 < d ∧ 1 ≤ i then κ ⟨i - 1, h.1⟩ else 0

/-- The condition defining `d'` (p.10 line 390) at the index `i`:
`6·((2d+1)/(2d))·κ_i·log((3d/q)·((2d+1)/(2d))·κ_i) < κ_{i+1}`. -/
def DPrimeCond (κ : Fin d → ℚ) (q : ℚ) (i : ℕ) : Prop :=
  6 * ((2 * (d : ℝ) + 1) / (2 * d)) * (kap κ i : ℝ) *
      Real.logb 2 (3 * d / (q : ℝ) * ((2 * (d : ℝ) + 1) / (2 * d)) * (kap κ i : ℝ)) <
    (kap κ (i + 1) : ℝ)

/-- `d'`: the smallest index in `{1, …, d − 1}` satisfying `DPrimeCond`, and `d` if there is none. -/
noncomputable def dPrime (κ : Fin d → ℚ) (q : ℚ) : ℕ := by
  classical
  exact if h : ∃ i, 1 ≤ i ∧ i ≤ d - 1 ∧ DPrimeCond κ q i then Nat.find h else d

/-- `K = ⌈(2d+1)κ_{d'}/(2d)⌉` (p.11 line 391). -/
noncomputable def numK (κ : Fin d → ℚ) (q : ℚ) : ℕ :=
  ⌈(2 * (d : ℚ) + 1) * kap κ (dPrime κ q) / (2 * d)⌉₊

/-- `R = ⌈log_{4/3}(3K/q)⌉` (p.11 line 391). -/
noncomputable def numR (κ : Fin d → ℚ) (q : ℚ) : ℕ :=
  ⌈Real.logb (4 / 3) (3 * (numK κ q : ℝ) / q)⌉₊

/-- `γ = 6d·log(3dK/q)` (Algorithm 1, line 3). -/
noncomputable def gammaPar (κ : Fin d → ℚ) (q : ℚ) : ℝ :=
  6 * d * Real.logb 2 (3 * d * (numK κ q : ℝ) / q)

/-- `G`, the least power of two at least `⌈γ⌉²` (Algorithm 1, line 4). -/
noncomputable def numG (κ : Fin d → ℚ) (q : ℚ) : ℕ := 2 ^ Nat.clog 2 (⌈gammaPar κ q⌉₊ ^ 2)

/-- `q₀ = q/(3R(KG + |J|))` (Algorithm 1, line 5). -/
noncomputable def failQ0 (κ : Fin d → ℚ) (q : ℚ) (nJ : ℕ) : ℚ :=
  q / (3 * numR κ q * (numK κ q * numG κ q + nJ))

/-- The recursive explicit target `u_i = (4d+2)κ_i/(dKε)` for the paper's index `i > d'`
(p.11 line 397), `ε = 2^{−ℓ}`. -/
noncomputable def uTarget (ℓ : ℕ) (κ : Fin d → ℚ) (q : ℚ) (i : ℕ) : ℚ :=
  (4 * d + 2) * kap κ i * 2 ^ ℓ / (d * numK κ q)

/-- The targets `(u, Σ(B'))` of a recursive call on `d − d' + 1` machines: coordinate `t < d − d'`
is `u_{d'+1+t}`, the last coordinate is the implicit machine with target `Σ(B')`. -/
noncomputable def recTargets (ℓ : ℕ) (κ : Fin d → ℚ) (q : ℚ) (B' : Multiset ℕ) :
    Fin (d - dPrime κ q + 1) → ℚ :=
  fun t => if (t : ℕ) < d - dPrime κ q then uTarget ℓ κ q (dPrime κ q + 1 + t) else (B'.sum : ℚ)

/-- `π` (p.11 lines 398–400): discard the implicit (last) coordinate, keep the points whose
explicit coordinates are at most `u_i` plus the call's error bound, and cap each coordinate at
`u_i`. -/
noncomputable def piProj (ℓ C₁ c₁ : ℕ) (κ : Fin d → ℚ) (q : ℚ) (B' : Multiset ℕ) (q₀ : ℚ)
    (T : Finset (Fin (d - dPrime κ q + 1) → ℚ)) : Finset (Fin (d - dPrime κ q) → ℚ) := by
  classical
  exact (T.filter fun x => ∀ t : Fin (d - dPrime κ q),
      (x t.castSucc : ℝ) ≤ (recTargets ℓ κ q B' t.castSucc : ℝ) +
        cpError ℓ C₁ c₁ B' (recTargets ℓ κ q B') q₀ t.castSucc).image
    fun x t => min (x t.castSucc) (recTargets ℓ κ q B' t.castSucc)

/-- The vector of `ℚ^d` with first `d'` coordinates `a·e_i` (or `0` when `i₀ = none`) and last
`d − d'` coordinates `y` (the `×` of lines 15 and 19). -/
noncomputable def place (κ : Fin d → ℚ) (q : ℚ) (a : ℚ) (i₀ : Option (Fin d))
    (y : Fin (d - dPrime κ q) → ℚ) : Fin d → ℚ :=
  fun i => if h : dPrime κ q ≤ (i : ℕ) ∧ (i : ℕ) - dPrime κ q < d - dPrime κ q then
      y ⟨(i : ℕ) - dPrime κ q, h.2⟩
    else if i₀ = some i then a else 0

/-- Line 21: `S ∪ {0_d} ∪ {x_j e_j : x ∈ S, 1 ≤ j ≤ d}`. -/
noncomputable def axisClose (S : Finset (Fin d → ℚ)) : Finset (Fin d → ℚ) := by
  classical
  exact S ∪ {0} ∪ S.biUnion fun x => Finset.univ.image fun j => Pi.single j (x j)

/-- A recursive call, with an empty job set handled directly by its exact profile set `{0}`. -/
noncomputable def callOrZero (cp : CPProcedure) (ℓ k : ℕ) (B' : Multiset ℕ) (t : Fin k → ℚ)
    (q₀ : ℚ) : PMF (Finset (Fin k → ℚ)) :=
  if B' = 0 then PMF.pure {0} else cp ℓ k B' t q₀

/-- The law of the leaf set `S^{(r)}_{ℓ,g}` for the job multiset `B = J^{(r)}_{ℓ,g}`
(Algorithm 1, lines 10–21), where `nJ = |J|` enters only through `q₀`. -/
noncomputable def leafLaw (cp : CPProcedure) (ℓ C₁ c₁ : ℕ) (κ : Fin d → ℚ) (q : ℚ) (nJ : ℕ)
    (B : Multiset ℕ) : PMF (Finset (Fin d → ℚ)) := by
  classical
  exact
    if dPrime κ q = d then
      -- line 12: `{0} ∪ {a e_i : a ∈ supp(B), 1 ≤ i ≤ d}`, then line 21
      PMF.pure (axisClose (insert 0 (B.toFinset.biUnion fun a =>
        Finset.univ.image fun i => Pi.single i (a : ℚ))))
    else
      let k := d - dPrime κ q + 1
      let q₀ := failQ0 κ q nJ
      -- line 14: the zero-choice call; lines 17–18: one call per distinct size `a`
      (callOrZero cp ℓ k B (recTargets ℓ κ q B) q₀).bind fun T0 =>
      ((B.toFinset.toList).mapM fun a =>
          (callOrZero cp ℓ k (B.erase a) (recTargets ℓ κ q (B.erase a)) q₀).map fun T => (a, T)).bind
        fun Ts =>
        -- line 15: `S₀ = {0_{d'}} × π(T0)`; line 19: `S_a = ⋃_{i ≤ d'} {a e_i} × π(T_a)`;
        -- line 20: their union; line 21: add `0_d` and the axis projections
        PMF.pure (axisClose
          ((piProj ℓ C₁ c₁ κ q B q₀ T0).image (place κ q 0 none) ∪
            (Ts.map fun aT =>
              (Finset.univ.filter fun i : Fin d => (i : ℕ) < dPrime κ q).biUnion fun i =>
                (piProj ℓ C₁ c₁ κ q (B.erase aT.1) q₀ aT.2).image
                  (place κ q (aT.1 : ℚ) (some i))).foldr (· ∪ ·) ∅))

/-- A uniform label in `{0, …, K − 1}` (`0` if `K = 0`). -/
noncomputable def uniformLabel (K : ℕ) : PMF ℕ :=
  if h : 0 < K then PMF.uniformOfFinset (Finset.range K) ⟨0, Finset.mem_range.2 h⟩ else PMF.pure 0

/-- A random partition of `N` occurrences into `K` parts: independent uniform labels. -/
noncomputable def randomPartition (N K : ℕ) : PMF (Fin N → ℕ) :=
  ((List.finRange N).mapM fun _ => uniformLabel K).map fun l j => l.getD j 0

/-- The multiset `J^{(r)}_{ℓ,g}` of the sizes of the occurrences with first-layer label `lv` and
second-layer label `g`. -/
noncomputable def subJobs (J : List ℕ) (f g : Fin J.length → ℕ) (lv gv : ℕ) : Multiset ℕ := by
  classical
  exact ((Finset.univ.filter fun j => f j = lv ∧ g j = gv).val.map fun j => J.get j)

/-- **Algorithm 1** with exact set expressions: the distribution of
`S = ∑_{ℓ<K} ⋃_{r<R} ∑_{g<G} S^{(r)}_{ℓ,g}`. -/
noncomputable def algorithm1 (cp : CPProcedure) (ℓ C₁ c₁ : ℕ) (J : List ℕ) (κ : Fin d → ℚ)
    (q : ℚ) : PMF (Set (Fin d → ℚ)) := by
  classical
  exact
    let K := numK κ q
    let R := numR κ q
    let G := numG κ q
    let triples : List (ℕ × ℕ × ℕ) :=
      (List.range R).flatMap fun r => (List.range K).flatMap fun lv =>
        (List.range G).map fun gv => (r, lv, gv)
    -- line 2: the first-layer partition; line 8: one second-layer partition per repetition
    (randomPartition J.length K).bind fun f =>
    ((List.range R).mapM fun _ => randomPartition J.length G).bind fun gs =>
    (triples.mapM fun x =>
        (leafLaw cp ℓ C₁ c₁ κ q J.length
          (subJobs J f (gs.getD x.1 fun _ => 0) x.2.1 x.2.2)).map fun L => (x, L)).bind
      fun leaves =>
      let leaf : ℕ → ℕ → ℕ → Finset (Fin d → ℚ) := fun r lv gv =>
        ((leaves.find? fun e => e.1 = (r, lv, gv)).map Prod.snd).getD ∅
      PMF.pure (∑ lv ∈ Finset.range K, ⋃ r ∈ Finset.range R,
        ∑ gv ∈ Finset.range G, ((leaf r lv gv : Finset (Fin d → ℚ)) : Set (Fin d → ℚ)))

end RelatedSchedFPTAS796.Main


