-- Prove2me | Definitions.Def_GMMIsoSample_Main_Clustering
-- name    : GMMIsoSample_Main_Clustering
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:32:06.333866+00:00
-- url     : https://prove2.me/theorems/cdcd13f8-debe-4082-b58a-bf04cca6e78e
-- title:
--   ExactClustering and its modules: RadiusGrouping, CountClusters*, CountClusters (reading), the SDP (81), ClusterRadiusGroup, ClusterMoreSamplePoints
-- statement:
--   Constants: $\gamma_d=(\log d)^{10}/\sqrt d$, $\tau=(\log d)^{11}/\sqrt d$ (53), $\rho=3\tau$, and $N_{EC}=2\lceil P\cdot(d/\Gamma_0^4)(\log d)^{20}\rceil$ (6) for a value $P=P(k_{\max},1/w_{\min})$. A nonempty set $J$ of components is **$\tau$-compatible** (Definition 19) if $\max_{i\in J}\sigma_i^2/\min_{j\in J}\sigma_j^2\le1+\tau$. A clustering is a set of blocks of sample indices; the correct one, `trueBlocks z`, is the set of nonempty label classes, and **exact clustering** means the output is that set and every component is present.
--
--   **RadiusGrouping** (Figure 6) repeatedly takes the remaining index set $R$ (failure if $|R|=1$), computes $D_R(t)=\min_{s\in R\setminus\{t\}}\|X_t-X_s\|^2$, its distinct values $y_1<\dots<y_h$, the least $j^\star$ with $y_{j^\star+1}\ge(1+\gamma_d)y_{j^\star}$ (else $h$), outputs $C=\{t:D_R(t)\le y_{j^\star}\}$ with $\hat s^2$ the largest integer power of $1+\tau$ that is at most $y_1/(2d(1+\gamma_d))$, and removes $C$. `RadiusGroupingGood` is the conclusion of Theorem 20.
--
--   **CountClusters\*** (Figure 7) returns the least $q\le k_{\max}$ with $(\mathrm{cost}_q+dq)-(\mathrm{cost}_{k_{\max}}+dk_{\max})\le L/8$, $L=w_{\min}m\Gamma_0^2/2$, where
--   $$\mathrm{cost}_q(X)=\min_{\mathcal P}\sum_{T\in\mathcal P}\frac1{2|T|}\sum_{u,v\in T}\|x_u-x_v\|^2$$
--   over partitions of $[m]$ into exactly $q$ nonempty sets (73). **CountClusters** is not defined in the paper; here it divides the points by $\hat s$, splits them in input order into $B=\max(1,\lceil A\log d\rceil)$ blocks of $\lfloor m/B\rfloor$ points, runs CountClusters\* on each and returns the most frequent answer (smallest on ties).
--
--   **ClusterRadiusGroup** (Figure 8) outputs the single block for $q=1$; otherwise it takes any optimal $\hat Z$ of the SDP (81): maximize $\mathrm{tr}(YY^\top Z)$ over symmetric $Z\succeq0$, $Z\ge0$ entrywise, $Z\mathbf 1=\mathbf 1$, $\mathrm{tr}Z=q$, and returns the classes of $i\sim j\iff\hat Z_{ij}>0$ (failure unless an equivalence with exactly $q$ classes). **ExactClustering** (Figure 5) runs RadiusGrouping, then CountClusters and ClusterRadiusGroup on each group, and returns all blocks. **ClusterMoreSamplePoints** (Figure 2) takes a uniformly random anchor $H$ of $N_{EC}/2$ reference points, splits the fresh sample into $L=2M/N_{EC}$ random batches $T_\ell$ of size $N_{EC}/2$, runs ExactClustering on $H\sqcup T_\ell$, matches each batch's blocks to the reference blocks through their intersection with $H$, and adds each batch's points to the matching reference block. $N_{CMS,2}=C(1/\varepsilon^2+\sqrt d/(\varepsilon\Gamma_{\min}))\log(100/\delta)$ (15) and $N_{CMS,k_{\max}}=C(\sqrt d/\varepsilon^2)\log(k_{\max}/\delta)$ (16) with $\delta=1/100$.
--
--   **Formalization Note.** Algorithms with a free choice (the SDP optimizer) are given as the set of all outputs they can produce, and every statement holds for all of them; failure is `none`. The RadiusGrouping loop has a bound of $N$ rounds, never reached since each round removes a point. $\log$ is natural. Indices are 0-based.
-- source:
--   Chen, De, Lee, Servedio, Sublinear Sample Size Suffices for Learning Mixtures of Gaussians up to Isometry, STOC 2027 submission (version of November 3, 2026, sha256 411f3581…), p. 6, (6); p. 19, Figure 2 and (15)–(16) (p. 16); p. 35, Figure 5 and Definition 19; p. 36, (53); p. 40, Figure 6; pp. 46–47, (73) and Figure 7; pp. 53–54, (81) and Figure 8

import Mathlib
import Definitions.Def_GMMIsoSample_Main_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GMMIsoSample.Main

/-!
# The exact-clustering algorithms of Part I

Chen, De, Lee, Servedio, *Sublinear Sample Size Suffices for Learning Mixtures of Gaussians up to
Isometry*, STOC 2027 submission (version of November 3, 2026, sha256 411f3581…): NEC (6), p. 6;
ExactClustering (Figure 5) and Definition 19, p. 35; τ (53), p. 36; RadiusGrouping (Figure 6),
p. 40; cost_p (73) and CountClusters* (Figure 7), pp. 46–47; the SDP (81) and
ClusterRadiusGroup (Figure 8), pp. 53–54; ClusterMoreSamplePoints (Figure 2), p. 19.

Conventions.
* A sample of `N` points is `X : Fin N → ℝ^d` (0-based indices); a clustering is the set of its
  blocks, a `Finset (Finset (Fin N))` of index sets. The correct clustering of a labelled sample
  with labels `z` is `trueBlocks z`, the set of nonempty label classes.
* Algorithms that leave a choice free (the optimizer of the SDP (81), hence ExactClustering and
  ClusterMoreSamplePoints) are given by the **set of all outputs** they can produce;
  guarantees are stated for every output in that set. `none` is failure.
* RadiusGrouping stores `ŝ²` (not `ŝ`). It runs at most `N` rounds; every round removes at least
  one point, so this bound is never reached on an input with `R = [N]`.
* CountClusters is not defined in the paper (finding I1). It is read here as: divide the points
  by `ŝ`, split them in input order into `B = max 1 ⌈A log d⌉` consecutive blocks of `⌊m/B⌋`
  points (the remainder unused), run CountClusters* on every block and return the most frequent
  answer, the smallest one on ties. `A > 0` is the amplification constant.
* `log` is the natural logarithm.
-/

/-- `γ_d = (log d)^10 / √d` (Figure 6). -/
noncomputable def gammaD (d : ℕ) : ℝ := Real.log d ^ 10 / Real.sqrt d

/-- `τ = (log d)^11 / √d` (53). (`ρ = 3τ`.) -/
noncomputable def tauD (d : ℕ) : ℝ := Real.log d ^ 11 / Real.sqrt d

/-- `NEC = 2⌈P · (d/Γ₀⁴) · (log d)^20⌉` (6), with `P` the value `P(kmax, 1/wmin)`. -/
noncomputable def nEC (P : ℝ) (d : ℕ) (Γ₀ : ℝ) : ℕ :=
  2 * ⌈P * ((d : ℝ) / Γ₀ ^ 4) * Real.log d ^ 20⌉₊

/-- `J ⊆ [k]` is `τ`-compatible (Definition 19): nonempty and
`max_{i∈J} σ_i² / min_{j∈J} σ_j² ≤ 1 + τ`. -/
def IsTauCompatible {d k : ℕ} (p : Params d k) (J : Finset (Fin k)) (τ : ℝ) : Prop :=
  J.Nonempty ∧ ∀ i ∈ J, ∀ j ∈ J, rad p i ^ 2 ≤ (1 + τ) * rad p j ^ 2

/-- The correct clustering of a labelled sample: the nonempty label classes. -/
def trueBlocks {N k : ℕ} (z : Fin N → Fin k) : Finset (Finset (Fin N)) :=
  Finset.univ.image (fun t => Finset.univ.filter (fun s => z s = z t))

/-- Exact clustering (Theorem 4): the output partitions the sample into `k` nonempty groups that
are exactly the true components' sample points. -/
def IsExactClustering {N k : ℕ} (z : Fin N → Fin k) (o : Option (Finset (Finset (Fin N)))) :
    Prop :=
  o = some (trueBlocks z) ∧ ∀ i : Fin k, ∃ t, z t = i

/-! ## RadiusGrouping (Figure 6) -/

/-- `D_R(t) = min_{s ∈ R∖{t}} ‖X_t − X_s‖²`. -/
noncomputable def nnDist {d N : ℕ} (X : Fin N → E d) (R : Finset (Fin N)) (t : Fin N) : ℝ :=
  sInf ((((R.erase t).image (fun s => ‖X t - X s‖ ^ 2)) : Finset ℝ) : Set ℝ)

/-- `y_{j⋆}` for the distinct values `Y = {y₁ < ⋯ < y_h}`: the least `y_j` whose successor is at
least `(1 + γ) y_j`, or `y_h` if there is none. -/
noncomputable def gapThreshold (γ : ℝ) (Y : Finset ℝ) : ℝ :=
  open Classical in
  sInf (((Y.filter (fun y => ∀ y' ∈ Y, y < y' → (1 + γ) * y ≤ y')) : Finset ℝ) : Set ℝ)

/-- `ŝ²`: the largest integer power of `1 + τ` that is at most `y₁ / (2d(1 + γ))`. -/
noncomputable def scaleEstimate (d : ℕ) (γ τ y₁ : ℝ) : ℝ :=
  (1 + τ) ^ (⌊Real.logb (1 + τ) (y₁ / (2 * d * (1 + γ)))⌋)

/-- The rounds of RadiusGrouping on the remaining index set `R`, with at most `fuel` rounds. -/
noncomputable def radiusGroupingAux {d N : ℕ} (X : Fin N → E d) (γ τ : ℝ) :
    ℕ → Finset (Fin N) → Option (List (Finset (Fin N) × ℝ))
  | 0, R => if R = ∅ then some [] else none
  | fuel + 1, R =>
    open Classical in
    if R = ∅ then some []
    else if R.card = 1 then none
    else
      let Y := R.image (nnDist X R)
      let thr := gapThreshold γ Y
      let C := R.filter (fun t => nnDist X R t ≤ thr)
      let s2 := scaleEstimate d γ τ (sInf (Y : Set ℝ))
      (radiusGroupingAux X γ τ fuel (R.filter (fun t => thr < nnDist X R t))).map
        (fun L => (C, s2) :: L)

/-- RadiusGrouping(X) (Figure 6): the list of pairs `(C_h, ŝ_h²)`, or failure (`none`). -/
noncomputable def radiusGrouping {d N : ℕ} (X : Fin N → E d) :
    Option (List (Finset (Fin N) × ℝ)) :=
  radiusGroupingAux X (gammaD d) (tauD d) N Finset.univ

/-- The guarantee of Theorem 20 holds for the output `out` of RadiusGrouping on a sample with
labels `z` from the mixture `p`: `out` is a list of `H ≤ k` pairs `(C_h, ŝ_h²)` whose `C_h`
partition the sample into nonempty sets, and some partition `[k] = I₁ ⊔ ⋯ ⊔ I_H` into nonempty
sets has every `I_h` `τ`-compatible, `C_h` = the sample points drawn from components in `I_h`,
and `ŝ_h²` an integer power of `1 + τ` with `1 ≤ σ_j²/ŝ_h² ≤ 1 + 3τ` for every `j ∈ I_h`. -/
def RadiusGroupingGood {d k N : ℕ} (p : Params d k) (τ : ℝ) (z : Fin N → Fin k)
    (out : Option (List (Finset (Fin N) × ℝ))) : Prop :=
  ∃ L : List (Finset (Fin N) × ℝ), out = some L ∧ L.length ≤ k ∧
    (∀ h : Fin L.length, (L.get h).1.Nonempty) ∧
    (∀ t : Fin N, ∃! h : Fin L.length, t ∈ (L.get h).1) ∧
    ∃ I : Fin L.length → Finset (Fin k),
      (∀ h, (I h).Nonempty) ∧ (∀ i : Fin k, ∃! h, i ∈ I h) ∧
      ∀ h, IsTauCompatible p (I h) τ ∧
        (L.get h).1 = Finset.univ.filter (fun t => z t ∈ I h) ∧
        (∃ n : ℤ, (L.get h).2 = (1 + τ) ^ n) ∧
        ∀ j ∈ I h, 1 ≤ rad p j ^ 2 / (L.get h).2 ∧ rad p j ^ 2 / (L.get h).2 ≤ 1 + 3 * τ

/-! ## CountClusters* (Figure 7) and CountClusters (reading, finding I1) -/

/-- `cost_p(X, 𝒫) = Σ_{T ∈ 𝒫} (1/(2|T|)) Σ_{u,v ∈ T} ‖x_u − x_v‖²` (73). -/
noncomputable def partCost {d m : ℕ} (x : Fin m → E d)
    (P : Finpartition (Finset.univ : Finset (Fin m))) : ℝ :=
  ∑ T ∈ P.parts, (1 / (2 * (T.card : ℝ))) * ∑ u ∈ T, ∑ v ∈ T, ‖x u - x v‖ ^ 2

/-- `cost_q(X)`: the minimum of `cost_q(X, 𝒫)` over partitions `𝒫` of `[m]` into exactly `q`
nonempty sets (a minimum over a finite nonempty set when `1 ≤ q ≤ m`). -/
noncomputable def cost {d m : ℕ} (q : ℕ) (x : Fin m → E d) : ℝ :=
  sInf {c | ∃ P : Finpartition (Finset.univ : Finset (Fin m)), P.parts.card = q ∧ partCost x P = c}

/-- CountClusters*(kmax, wmin, Γ₀; x₁, …, x_m) (Figure 7): the smallest `q ∈ [kmax]` with
`(cost_q(X) + dq) − (cost_kmax(X) + d·kmax) ≤ L/8`, `L = wmin m Γ₀² / 2`. (Its input `ρ` is not
used by any step of Figure 7 and is omitted.) -/
noncomputable def countClustersStar {d m : ℕ} (kmax : ℕ) (wmin Γ₀ : ℝ) (x : Fin m → E d) : ℕ :=
  sInf {q : ℕ | 1 ≤ q ∧ q ≤ kmax ∧
    (cost q x + d * q) - (cost kmax x + d * kmax) ≤ (wmin * m * Γ₀ ^ 2 / 2) / 8}

/-- CountClusters(ŝ, C) under the reading of finding I1, with amplification constant `A`: the
points divided by `ŝ` are split in input order into `B = max 1 ⌈A log d⌉` consecutive blocks of
`⌊m/B⌋` points; CountClusters* runs on each block; the most frequent answer is returned (the
smallest on ties). -/
noncomputable def countClusters {d m : ℕ} (A : ℝ) (kmax : ℕ) (wmin Γ₀ : ℝ) (s : ℝ)
    (x : Fin m → E d) : ℕ :=
  let B : ℕ := max 1 ⌈A * Real.log d⌉₊
  let b : ℕ := m / B
  let xs : ℕ → E d := fun n => if h : n < m then s⁻¹ • x ⟨n, h⟩ else 0
  let ans : Fin B → ℕ := fun j =>
    countClustersStar kmax wmin Γ₀ (fun u : Fin b => xs (j.1 * b + u.1))
  let votes : ℕ → ℕ := fun q => (Finset.univ.filter (fun j => ans j = q)).card
  sInf {q : ℕ | 1 ≤ q ∧ q ≤ kmax ∧ ∀ q', 1 ≤ q' → q' ≤ kmax → votes q' ≤ votes q}

/-! ## ClusterRadiusGroup (Figure 8) and the SDP (81) -/

/-- `A = Y Yᵀ`, the Gram matrix of the points. -/
noncomputable def gramMat {d m : ℕ} (Y : Fin m → E d) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => inner ℝ (Y i) (Y j)

/-- Feasibility for (81): `Z` symmetric positive semidefinite, entrywise nonnegative, `Z𝟏 = 𝟏`,
`tr Z = q`. (`PosSemidef` includes symmetry.) -/
def SDPFeasible {m : ℕ} (q : ℕ) (Z : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  Z.PosSemidef ∧ (∀ i j, 0 ≤ Z i j) ∧ (∀ i, ∑ j, Z i j = 1) ∧ Z.trace = q

/-- `Z` is an optimal solution of (81): feasible and maximizing `⟨A, Z⟩ = tr(AZ)`. -/
def SDPOptimal {d m : ℕ} (Y : Fin m → E d) (q : ℕ) (Z : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  SDPFeasible q Z ∧ ∀ Z', SDPFeasible q Z' → (gramMat Y * Z').trace ≤ (gramMat Y * Z).trace

/-- The classes `{j : Ẑ_ij > 0}`. -/
noncomputable def classesOf {m : ℕ} (Z : Matrix (Fin m) (Fin m) ℝ) : Finset (Finset (Fin m)) :=
  open Classical in
  Finset.univ.image (fun i => Finset.univ.filter (fun j => 0 < Z i j))

/-- Figure 8, last step: the classes of `i ∼ j ⟺ Ẑ_ij > 0`, or failure if `∼` is not an
equivalence relation with exactly `q` classes. -/
noncomputable def readPartition {m : ℕ} (q : ℕ) (Z : Matrix (Fin m) (Fin m) ℝ) :
    Option (Finset (Finset (Fin m))) :=
  open Classical in
  if (∀ i, 0 < Z i i) ∧ (∀ i j, 0 < Z i j → 0 < Z j i) ∧
      (∀ i j l, 0 < Z i j → 0 < Z j l → 0 < Z i l) ∧ (classesOf Z).card = q
  then some (classesOf Z) else none

/-- ClusterRadiusGroup(Y₁, …, Y_m; q) (Figure 8): every output it can produce. For `q = 1` the
single block `[m]`; otherwise the partition read off any optimal solution of (81); failure if (81)
has no optimal solution. -/
noncomputable def crgOutputs {d m : ℕ} (Y : Fin m → E d) (q : ℕ) :
    Set (Option (Finset (Finset (Fin m)))) :=
  open Classical in
  if q = 1 then {some {Finset.univ}}
  else if ∃ Z, SDPOptimal Y q Z then {o | ∃ Z, SDPOptimal Y q Z ∧ o = readPartition q Z}
  else {none}

/-! ## ExactClustering (Figure 5) -/

/-- ExactClustering(kmax, wmin, Γ₀, X) (Figure 5), with CountClusters read with amplification
constant `A`: every output it can produce. Step 1 RadiusGrouping; Step 2
`k̂_h = CountClusters(ŝ_h, C_h)` (points of `C_h` in increasing index order); Step 3
`P_h ∈ ClusterRadiusGroup(C_h, k̂_h)`; Step 4 all blocks of `P₁, …, P_H` (as index sets of `X`);
failure if any module fails. -/
noncomputable def exactClusteringOutputs {d N : ℕ} (A : ℝ) (kmax : ℕ) (wmin Γ₀ : ℝ)
    (X : Fin N → E d) : Set (Option (Finset (Finset (Fin N)))) :=
  match radiusGrouping X with
  | none => {none}
  | some L =>
    let emb : (h : Fin L.length) → Fin (L.get h).1.card ↪o Fin N :=
      fun h => (L.get h).1.orderEmbOfFin rfl
    let Y : (h : Fin L.length) → Fin (L.get h).1.card → E d := fun h u => X (emb h u)
    let q : Fin L.length → ℕ :=
      fun h => countClusters A kmax wmin Γ₀ (Real.sqrt (L.get h).2) (Y h)
    {o | (∃ h, none ∈ crgOutputs (Y h) (q h)) ∧ o = none} ∪
    {o | ∃ Q : (h : Fin L.length) → Finset (Finset (Fin (L.get h).1.card)),
      (∀ h, some (Q h) ∈ crgOutputs (Y h) (q h)) ∧
      o = some (Finset.univ.biUnion (fun h => (Q h).image (fun B => B.map (emb h).toEmbedding)))}

/-! ## ClusterMoreSamplePoints (Figure 2) -/

/-- `N_CMS,2 = C (1/ε² + √d/(εΓmin)) log(100/δ)` (15), `δ = 1/100`. -/
noncomputable def nCMS2 (C ε : ℝ) (d : ℕ) (Γmin : ℝ) : ℝ :=
  C * (1 / ε ^ 2 + Real.sqrt d / (ε * Γmin)) * Real.log (100 / (1 / 100))

/-- `N_CMS,kmax = C (√d/ε²) log(kmax/δ)` (16), `δ = 1/100`. -/
noncomputable def nCMSk (C ε : ℝ) (d kmax : ℕ) : ℝ :=
  C * (Real.sqrt d / ε ^ 2) * Real.log (kmax / (1 / 100))

/-- ClusterMoreSamplePoints(X, S₁, …, S_k) (Figure 2): every output it can produce. The combined
sample is indexed by `Fin (n + M)`: the reference sample `S` (size `n = NEC`) is `castAdd`, the
fresh sample `X` (size `M`) is `natAdd`; `blocks` is the reference clustering returned by
ExactClustering on `S`. The anchor `H` is the first `n/2` reference indices in the order of the
uniform permutation `π₁`; the batches `T_ℓ` (`ℓ < L = M/(n/2) = 2M/n`) are consecutive runs of
`n/2` fresh indices in the order of the uniform permutation `π₂`; batch `ℓ` is clustered by
ExactClustering on `H` followed by `T_ℓ`. The output maps each reference block `S_i` to its
extension `S'_i`. -/
noncomputable def clusterMoreOutputs {d n M : ℕ} (A : ℝ) (kmax : ℕ) (wmin Γ₀ : ℝ)
    (pos : Fin (n + M) → E d) (blocks : Finset (Finset (Fin n)))
    (π₁ : Equiv.Perm (Fin n)) (π₂ : Equiv.Perm (Fin M)) :
    Set (Option (Finset (Fin n) → Finset (Fin (n + M)))) :=
  open Classical in
  let h : ℕ := n / 2
  let L : ℕ := M / h
  let Hl : List (Fin (n + M)) := (((List.finRange n).map π₁).take h).map (Fin.castAdd M)
  let Tl : ℕ → List (Fin (n + M)) := fun ℓ =>
    ((((List.finRange M).map π₂).drop (ℓ * h)).take h).map (Fin.natAdd n)
  let bl : Fin L → List (Fin (n + M)) := fun ℓ => Hl ++ Tl ℓ.1
  let Hset : Finset (Fin (n + M)) := Hl.toFinset
  let HB : Finset (Fin n) → Finset (Fin (n + M)) := fun B => B.image (Fin.castAdd M) ∩ Hset
  let G : (ℓ : Fin L) → Finset (Fin (bl ℓ).length) → Finset (Fin (n + M)) :=
    fun ℓ C => C.image (bl ℓ).get
  let ok : (ℓ : Fin L) → Finset (Finset (Fin (bl ℓ).length)) → Prop := fun ℓ Q =>
    Q.card = blocks.card ∧ ∀ B ∈ blocks, ∃ C ∈ Q, G ℓ C ∩ Hset = HB B
  let ext : ((ℓ : Fin L) → Finset (Finset (Fin (bl ℓ).length))) →
      Finset (Fin n) → Finset (Fin (n + M)) := fun Q B =>
    B.image (Fin.castAdd M) ∪ Finset.univ.biUnion (fun ℓ : Fin L =>
      ((Q ℓ).filter (fun C => G ℓ C ∩ Hset = HB B)).biUnion
        (fun C => G ℓ C ∩ (Tl ℓ.1).toFinset))
  if ∃ B ∈ blocks, HB B = ∅ then {none}
  else
    {o | (∃ ℓ, none ∈ exactClusteringOutputs A kmax wmin Γ₀ (fun t => pos ((bl ℓ).get t))) ∧
        o = none} ∪
    {o | ∃ Q : (ℓ : Fin L) → Finset (Finset (Fin (bl ℓ).length)),
      (∀ ℓ, some (Q ℓ) ∈ exactClusteringOutputs A kmax wmin Γ₀ (fun t => pos ((bl ℓ).get t))) ∧
      o = if ∀ ℓ, ok ℓ (Q ℓ) then some (ext Q) else none}

/-- The conclusion of Lemma 11 for an output `o` of ClusterMoreSamplePoints on the reference
clustering `blocks`, with true labels `z` on the combined sample: `o` returns extensions `S'_i`
of the `k` reference blocks which form exactly the true clustering of the combined sample (every
component present), with `S_i ⊆ S'_i`. -/
def ClusterMoreCorrect {n M k : ℕ} (blocks : Finset (Finset (Fin n))) (z : Fin (n + M) → Fin k)
    (o : Option (Finset (Fin n) → Finset (Fin (n + M)))) : Prop :=
  ∃ ext, o = some ext ∧ blocks.card = k ∧ blocks.image ext = trueBlocks z ∧
    (∀ i : Fin k, ∃ t, z t = i) ∧ ∀ B ∈ blocks, B.image (Fin.castAdd M) ⊆ ext B

end GMMIsoSample.Main


