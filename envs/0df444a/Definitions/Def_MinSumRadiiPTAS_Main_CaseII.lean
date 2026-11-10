-- Prove2me | Definitions.Def_MinSumRadiiPTAS_Main_CaseII
-- name    : MinSumRadiiPTAS_Main_CaseII
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:05:25.694758+00:00
-- url     : https://prove2.me/theorems/0c9a5472-ea1b-4cef-bfdf-ddcaa9c16366
-- title:
--   Case II of §6.2: the preprocessing, certified balls $\mathcal C_R$, significant net points and the benchmark $O'$ with its random tape
-- statement:
--   Fix distances $d$, an opening cost $\lambda$, $\varepsilon$ and a radius bound $R$.
--
--   1. **Dense ball** (p. 25) `IsDense d λ R P″ p ρ`: $\mathrm{opt}^R_{f,\lambda}(\mathrm{Ball}(p, \rho) \cap P'') > 2(\rho + \lambda)$.
--   2. **Preprocessing** (p. 25): a run is the list of picked dense balls $(p_j, \rho_j)$; each pick adds $\mathrm{Ball}(p_j, \rho_j + 2R)$ to $S$ (`preBalls`) and removes its points from the client set (`preFinal` is the client set $P''$ left at the end). `IsPreprocessingRun d λ ε R P′ steps`: every pick is dense for the current client set with $\rho_j \in [2R, r_{\max} - 2R]$, and at the end no dense ball with radius in $[2R, r_{\max} - 2R]$ remains.
--   3. **Certified balls** (p. 26) `IsCertifiedR d λ R P″ C`: $C \in \mathfrak B$, $r_C \le 3R$ and $\mathrm{opt}^R_{f,\lambda}(C \cap P'') \ge (r_C + \lambda)/3$. `zoneR d λ R P″ lo hi` $= Z_i$ is the set of points of $P$ covered by certified balls with radius in $(\mathrm{lo}, \mathrm{hi}]$.
--   4. **Significant net point** (p. 11, p. 26) `IsSignificant d O a_i C_s`: no point of the chosen certified ball $C_s$ lies in a ball of $O$ of radius $> a_i$.
--   5. **The pipeline and the benchmark** (`PipelineData`: $d, \lambda, \varepsilon, R$, the client set $P''$, the comparison solution $O = O_{3R}$, and the ordered nets `nets σ i` $= N_i$). All randomness is read from one tape $\omega$ under the published `MinSumFPT.tapeLaw` (independent coordinates uniform on $[0,1]$), each source at its own coordinate: $\sigma = \min(L-1, \lfloor L u \rfloor)$ (uniform on $\{0,\dots,L-1\}$), thresholds $a_i$ with target $3R$ and $L = \lceil e^{7100}/\varepsilon\rceil$, top level $t$; the LDD radius $\ell_i = a_i(8 + u_i)$ (uniform on $[8a_i, 9a_i]$); $P_i = \mathrm{LDD}(P'', N_i, 8a_i, 9a_i)$; for each node $(X, i)$ a radius $D = U + 1 + \min(U-1, \lfloor U u\rfloor)$ (uniform on $\{U+1, \dots, 2U\}$, $U = 2^{3L}$) and independent uniform priorities of the active children (their order is a uniformly random permutation). Expansions $B^{\mathrm{par}} = \mathrm{Ball}(c_B, r_B + 11\,\mathrm{lo}_B)$, $B^{\mathrm{full}} = \mathrm{Ball}(c_B, r_B + 29\,\mathrm{lo}_B)$; weight $w(F) = \sum_{B \in F} ((r_B + 29\,\mathrm{lo}_B)/(1+\varepsilon) + \lambda)$ of a multiset (eq. (1), p. 14). $S_{X,i} = \{B \in O : r_B > a_i, B^{\mathrm{par}} \cap X \ne \emptyset\}$; the active children of $(X, i)$ are the near children $X \cap P_s \ne \emptyset$ met by no $B^{\mathrm{par}}$, $B \in S_{X,i}$; the proximity graph joins active children whose net points are within $22 a_i$; FormGroups groups them; $S_G = \{B \in O : a_{i-1} < r_B \le a_i, B^{\mathrm{par}} \cap \bigcup_{s \in G} (X \cap P_s) \ne \emptyset\}$. The benchmark `bench ω i X` (§5.2.1, p. 19) is, at a leaf, the zero-radius balls of the points of $X$ outside every $B^{\mathrm{full}}$, $B \in S_{X,0}$; at an internal node, the far child's benchmark (if the far part meets $X$) plus, for every group $G$, $S_G$ and the benchmarks of the children in $G$, with multiplicity. `benchmark ω` $= O'$ starts at the root $(P'', t)$. `NetsAdmissible` says that for every $\sigma < L$ and level $1 \le i \le t$, `nets σ i` lists without repetition a $6a_i$-net of $Z_i$.
--
--   **Formalization Note** In the paper FormGroups is called once per DP state $((X, i), S)$; the benchmark only looks at the call with $S = S_{X,i}$, so one independent draw per node gives the same law. Ties among the continuous priorities have probability $0$ and are broken by the point index.
-- source:
--   Fabrizio Grandoni, Anupam Gupta, Jatin Yadav, A PTAS for the Minimum Sum of Radii Problem, manuscript dated November 3, 2026 (STOC 2027 submission), SHA-256 99b43d49…, pp. 11–19 (§§4–5), pp. 24–27 (§6.2), pp. 36–37 (Appendix B)

import Mathlib
import Definitions.Def_MinSumRadiiPTAS_Main_LP
import Definitions.Def_MinSumRadiiPTAS_Main_Partition
import Definitions.Def_MinSumFPT_Machine

open scoped Classical

namespace MinSumRadiiPTAS.Main

/-!
# Case II of §6.2: preprocessing, certified balls, significance and the benchmark `O′`

Grandoni, Gupta, Yadav, *A PTAS for the Minimum Sum of Radii Problem* (STOC 2027 submission,
SHA-256 99b43d49…): p. 25 (dense balls, the preprocessing), p. 26 (thresholds with target `3R`,
the certified balls `C_R`, the partitions `P_i`), p. 11 and p. 26 (significant net points),
pp. 12–19 and pp. 36–37 (the hierarchical partition, partial/full expansions, the weight `w`,
ComputeDP's active children and proximity graph, the benchmark `O′`).

**Formalization Note.** A run of the preprocessing is the list of the dense balls `(p, ρ)` it picks,
in order; it is valid if every pick is dense for the current client set with `ρ ∈ [2R, r_max − 2R]`,
and terminated if no such dense ball remains. All randomness of the bounded-radius pipeline (the
threshold shift `σ`, one LDD radius per level, the FormGroups draws of every node) is read from one
random tape `ω : ℕ → ℝ` under the published law `MinSumFPT.tapeLaw` (independent coordinates,
uniform on `[0, 1]`), each source at its own coordinate (an injective `Encodable` code). From a
uniform coordinate `u`: `σ = min(L−1, ⌊L u⌋)` is uniform on `{0, …, L−1}`; `ℓ_i = a_i (8 + u)` is
uniform on `[8a_i, 9a_i]`; `D = U + 1 + min(U−1, ⌊U u⌋)` is uniform on `{U+1, …, 2U}`; the
random permutation of the active children of a node is the order of independent uniform priorities
(ties, a null event, broken by the point index), which is a uniformly random order. The benchmark
uses the FormGroups draw of the call `ComputeDP((X, i), S_{X,i})` only, so one draw per node. -/

/-- `Ball(p, ρ)` is dense for the client set `P″` (p. 25): `opt^R_{f,λ}(Ball(p, ρ) ∩ P″) > 2(ρ + λ)`. -/
def IsDense {n : ℕ} (d : Fin n → Fin n → ℝ) (lam R : ℝ) (P2 : Finset (Fin n)) (p : Fin n)
    (ρ : ℝ) : Prop :=
  2 * (ρ + lam) < optfR d lam R ((Ball.pts d ⟨p, ρ⟩) ∩ P2)

/-- The client set left after the picks `steps` (each pick `(p, ρ)` removes `Ball(p, ρ + 2R)`). -/
noncomputable def preFinal {n : ℕ} (d : Fin n → Fin n → ℝ) (R : ℝ) (P1 : Finset (Fin n))
    (steps : List (Fin n × ℝ)) : Finset (Fin n) :=
  steps.foldl (fun P2 st => P2 \ Ball.pts d ⟨st.1, st.2 + 2 * R⟩) P1

/-- The balls `S` of the preprocessing: `Ball(p, ρ + 2R)` for every pick `(p, ρ)`. -/
def preBalls {n : ℕ} (R : ℝ) (steps : List (Fin n × ℝ)) : List (Ball n) :=
  steps.map (fun st => ⟨st.1, st.2 + 2 * R⟩)

/-- `steps` is a terminated run of the preprocessing of §6.2 (p. 25) from the client set `P′`:
every pick is a dense ball (for the client set at that moment) with radius in `[2R, r_max − 2R]`,
and at the end no dense ball with radius in `[2R, r_max − 2R]` remains. -/
def IsPreprocessingRun {n : ℕ} (d : Fin n → Fin n → ℝ) (lam ε R : ℝ) (P1 : Finset (Fin n))
    (steps : List (Fin n × ℝ)) : Prop :=
  (∀ (j : ℕ) (hj : j < steps.length),
      2 * R ≤ (steps[j]).2 ∧ (steps[j]).2 ≤ rmax ε R - 2 * R ∧
        IsDense d lam R (preFinal d R P1 (steps.take j)) (steps[j]).1 (steps[j]).2) ∧
    ∀ (p : Fin n) (ρ : ℝ), 2 * R ≤ ρ → ρ ≤ rmax ε R - 2 * R →
      ¬ IsDense d lam R (preFinal d R P1 steps) p ρ

/-- `C ∈ C_R` (p. 26): `C ∈ 𝔅`, `r_C ≤ 3R` and `opt^R_{f,λ}(C ∩ P″) ≥ (r_C + λ)/3`. -/
def IsCertifiedR {n : ℕ} (d : Fin n → Fin n → ℝ) (lam R : ℝ) (P2 : Finset (Fin n))
    (C : Ball n) : Prop :=
  C ∈ minimalBalls d ∧ C.radius ≤ 3 * R ∧ (C.radius + lam) / 3 ≤ optfR d lam R (C.pts d ∩ P2)

/-- `Z_i` (p. 10, p. 26): the points of `P` covered by balls of `C_R` with radius in `(lo, hi]`
(`lo = a_{i−1}`, `hi = a_i`). -/
noncomputable def zoneR {n : ℕ} (d : Fin n → Fin n → ℝ) (lam R : ℝ) (P2 : Finset (Fin n))
    (lo hi : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => ∃ C : Ball n, IsCertifiedR d lam R P2 C ∧ lo < C.radius ∧
    C.radius ≤ hi ∧ p ∈ C.pts d)

/-- A net point with chosen certified ball `C_s` is significant at level `i` with respect to `O`
(p. 11, p. 26): no point of `C_s` lies in a ball of `O` of radius `> a_i`. -/
def IsSignificant {n : ℕ} (d : Fin n → Fin n → ℝ) (O : Finset (Ball n)) (ai : ℝ) (Cs : Ball n) :
    Prop :=
  ∀ q ∈ Cs.pts d, ∀ B ∈ O, ai < B.radius → q ∉ B.pts d

/-- The random sources of the bounded-radius pipeline: `σ`, the LDD radius of level `i`, the `D` of
the FormGroups call at node `(X, i)`, and the priority of the child with net point `s` there. -/
abbrev RandSrc (n : ℕ) : Type :=
  Unit ⊕ ℕ ⊕ (Finset (Fin n) × ℕ) ⊕ (Finset (Fin n) × ℕ × Fin n)

/-- The tape coordinate of a random source (an injective code). -/
def srcIdx {n : ℕ} (s : RandSrc n) : ℕ := Encodable.encode s

/-- The pipeline of Case II for fixed data, read off the tape `ω` (Appendix B and §§4–5 with the
§6.2 changes). `nets σ i` is the ordered `6a_i`-net `N_i` of `Z_i` used when the threshold shift is
`σ`. -/
structure PipelineData (n : ℕ) where
  /-- The distances. -/
  d : Fin n → Fin n → ℝ
  /-- The opening cost `λ`. -/
  lam : ℝ
  /-- The error parameter `ε`. -/
  ε : ℝ
  /-- The radius bound `R`. -/
  R : ℝ
  /-- The client set `P″` after the preprocessing. -/
  P2 : Finset (Fin n)
  /-- The comparison solution `O = O_{3R}`. -/
  O : Finset (Ball n)
  /-- The ordered nets: `nets σ i` is `N_i` for the shift `σ`. -/
  nets : ℕ → ℕ → List (Fin n)

namespace PipelineData

variable {n : ℕ} (A : PipelineData n)

/-- `L = ⌈e^{7100}/ε⌉`. -/
noncomputable def L : ℕ := L6 A.ε

/-- `σ = min(L − 1, ⌊L u⌋)` from the tape. -/
noncomputable def sigma (ω : ℕ → ℝ) : ℕ :=
  min (A.L - 1) ⌊(A.L : ℝ) * ω (srcIdx (Sum.inl () : RandSrc n))⌋₊

/-- The threshold `a_i` for the tape's `σ` (target `3R`). -/
noncomputable def a (ω : ℕ → ℝ) (i : ℕ) : ℝ := thr A.lam A.L (A.sigma ω) i

/-- The top level `t` for the tape's `σ`: the smallest positive integer with `a_t ≥ 3R` (p. 26). -/
noncomputable def top (ω : ℕ → ℝ) : ℕ := thrTop A.lam (3 * A.R) A.L (A.sigma ω)

/-- `lo_B` of a ball of radius `r` for the tape's `σ`. -/
noncomputable def lo (ω : ℕ → ℝ) (r : ℝ) : ℝ := loThr A.lam (3 * A.R) A.L (A.sigma ω) r

/-- The partial expansion `B^par = Ball(c_B, r_B + 11 lo_B)` (p. 14). -/
noncomputable def par (ω : ℕ → ℝ) (B : Ball n) : Ball n :=
  B.withRadius (B.radius + 11 * A.lo ω B.radius)

/-- The full expansion `B^full = Ball(c_B, r_B + 29 lo_B)` (p. 14). -/
noncomputable def full (ω : ℕ → ℝ) (B : Ball n) : Ball n :=
  B.withRadius (B.radius + 29 * A.lo ω B.radius)

/-- The weight `w(F) = ∑_{B ∈ F} ((r_B + 29 lo_B)/α + λ)`, `α = 1 + ε`, of a multiset of balls
(eq. (1), p. 14). -/
noncomputable def weight (ω : ℕ → ℝ) (F : Multiset (Ball n)) : ℝ :=
  (F.map (fun B => (B.radius + 29 * A.lo ω B.radius) / (1 + A.ε) + A.lam)).sum

/-- The LDD radius `ℓ_i = a_i (8 + u)` of level `i`. -/
noncomputable def ell (ω : ℕ → ℝ) (i : ℕ) : ℝ :=
  A.a ω i * (8 + ω (srcIdx (Sum.inr (Sum.inl i) : RandSrc n)))

/-- The near part `P_s` of `P_i = LDD(P″, N_i, 8a_i, 9a_i)`. -/
noncomputable def nearPart (ω : ℕ → ℝ) (i : ℕ) (s : Fin n) : Finset (Fin n) :=
  lddPart A.d A.P2 (A.nets (A.sigma ω) i) (A.ell ω i) s

/-- The far part of `P_i`. -/
noncomputable def farPart (ω : ℕ → ℝ) (i : ℕ) : Finset (Fin n) :=
  lddFar A.d A.P2 (A.nets (A.sigma ω) i) (A.ell ω i)

/-- `S_{X,i} = {B ∈ O : r_B > a_i, B^par ∩ X ≠ ∅}` (p. 19). -/
noncomputable def SX (ω : ℕ → ℝ) (X : Finset (Fin n)) (i : ℕ) : Finset (Ball n) :=
  A.O.filter (fun B => A.a ω i < B.radius ∧ ((A.par ω B).pts A.d ∩ X).Nonempty)

/-- The active near children of the visited node `(X, i)`, `i ≥ 1`, identified by their net points
(p. 15): `s ∈ N_i` with `X ∩ P_s ≠ ∅` such that no partial expansion of a ball of `S_{X,i}` meets
`X ∩ P_s`. -/
noncomputable def active (ω : ℕ → ℝ) (X : Finset (Fin n)) (i : ℕ) : Finset (Fin n) :=
  (A.nets (A.sigma ω) i).toFinset.filter (fun s => (X ∩ A.nearPart ω i s).Nonempty ∧
    ∀ B ∈ A.SX ω X i, ((A.par ω B).pts A.d ∩ (X ∩ A.nearPart ω i s)) = ∅)

/-- The proximity graph `H` of ComputeDP (Algorithm 4, line 5): active children are adjacent iff
their net points are within distance `22 a_i` (`SimpleGraph.fromRel` symmetrises the relation and
drops loops); all other points are isolated. -/
noncomputable def proxGraph (ω : ℕ → ℝ) (X : Finset (Fin n)) (i : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun u v => u ∈ A.active ω X i ∧ v ∈ A.active ω X i ∧
    A.d u v ≤ 22 * A.a ω i)

/-- `D = U + 1 + min(U − 1, ⌊U u⌋)`, `U = 2^{3L}`, for the FormGroups call at node `(X, i)`. -/
noncomputable def groupD (ω : ℕ → ℝ) (X : Finset (Fin n)) (i : ℕ) : ℕ :=
  U6 A.ε + 1 + min (U6 A.ε - 1)
    ⌊(U6 A.ε : ℝ) * ω (srcIdx (Sum.inr (Sum.inr (Sum.inl (X, i))) : RandSrc n))⌋₊

/-- The priority of the active child with net point `s` at node `(X, i)`. -/
noncomputable def prio (_A : PipelineData n) (ω : ℕ → ℝ) (X : Finset (Fin n)) (i : ℕ) (s : Fin n) : ℝ :=
  ω (srcIdx (Sum.inr (Sum.inr (Sum.inr (X, i, s))) : RandSrc n))

/-- The leader key of an active child in FormGroups (Algorithm 6): the least (priority, index)
among the active children within graph distance `D` of it. -/
noncomputable def leaderKey (ω : ℕ → ℝ) (X : Finset (Fin n)) (i : ℕ) (v : Fin n) :
    Option (Lex (ℝ × ℕ)) :=
  let S := ((A.active ω X i).filter (fun u =>
      (A.proxGraph ω X i).edist u v ≤ ((A.groupD ω X i : ℕ) : ℕ∞))).image
    (fun u => toLex (A.prio ω X i u, (u : ℕ)))
  if h : S.Nonempty then some (S.min' h) else none

/-- The groups formed by FormGroups at node `(X, i)`: active children with the same leader. -/
noncomputable def groups (ω : ℕ → ℝ) (X : Finset (Fin n)) (i : ℕ) : Finset (Finset (Fin n)) :=
  (A.active ω X i).image (fun v =>
    (A.active ω X i).filter (fun u => A.leaderKey ω X i u = A.leaderKey ω X i v))

/-- `S_G = {B ∈ O : a_{i−1} < r_B ≤ a_i, B^par ∩ ⋃_{j ∈ G} X_j ≠ ∅}` (p. 19). -/
noncomputable def SG (ω : ℕ → ℝ) (X : Finset (Fin n)) (i : ℕ) (G : Finset (Fin n)) :
    Finset (Ball n) :=
  A.O.filter (fun B => A.a ω (i - 1) < B.radius ∧ B.radius ≤ A.a ω i ∧
    ((A.par ω B).pts A.d ∩ G.biUnion (fun s => X ∩ A.nearPart ω i s)).Nonempty)

/-- The benchmark `O′_{X,i}` built at the visited node `(X, i)` and its descendants (§5.2.1, p. 19;
Appendix B): at a leaf, the zero-radius balls `Ball(p, 0)` of the points of `X` not covered by the
full expansions of `S_{X,0}`; at an internal node, the far child's benchmark (if the far part meets
`X`) plus, for every group `G`, the balls `S_G` and the benchmarks of the children of `G`.
Copies are counted with multiplicity. -/
noncomputable def bench (ω : ℕ → ℝ) : ℕ → Finset (Fin n) → Multiset (Ball n)
  | 0, X => ((X.filter (fun p => ∀ B ∈ A.SX ω X 0, p ∉ (A.full ω B).pts A.d)).val.map
      (fun p => (⟨p, 0⟩ : Ball n)))
  | i + 1, X =>
      (if (X ∩ A.farPart ω (i + 1)).Nonempty then bench ω i (X ∩ A.farPart ω (i + 1)) else 0) +
        ∑ G ∈ A.groups ω X (i + 1),
          ((A.SG ω X (i + 1) G).val + ∑ s ∈ G, bench ω i (X ∩ A.nearPart ω (i + 1) s))

/-- The benchmark `O′`, built from the root `(P″, t)`. -/
noncomputable def benchmark (ω : ℕ → ℝ) : Multiset (Ball n) := A.bench ω (A.top ω) A.P2

/-- The nets are admissible: for every shift `σ ∈ {0, …, L−1}` and level `i ∈ {1, …, t}`,
`nets σ i` lists without repetition a `6a_i`-net of `Z_i` (p. 11, p. 26). -/
def NetsAdmissible : Prop :=
  ∀ σ < A.L, ∀ i, 1 ≤ i → i ≤ thrTop A.lam (3 * A.R) A.L σ →
    (A.nets σ i).Nodup ∧
      IsNet A.d (zoneR A.d A.lam A.R A.P2 (thr A.lam A.L σ (i - 1)) (thr A.lam A.L σ i))
        (A.nets σ i).toFinset (6 * thr A.lam A.L σ i)

end PipelineData

end MinSumRadiiPTAS.Main


