-- Prove2me | Definitions.Def_PrivRobustStat_Filter
-- name    : PrivRobustStat_Filter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:49:06.021867+00:00
-- url     : https://prove2.me/theorems/ed52d5a2-e961-41c0-9fd2-c1e59a54da6f
-- title:
--   Algorithms 1–4: PrivateMultiply, PrivateScores, PrivateSoftFilter (loop and binary search), PrivateFastCovFilter
-- statement:
--   The private covariance filter of §3 as functions of the private data $x_{[n]}$, a public centre $c$ (with $M_i=(x_i-c)(x_i-c)^\top$), public parameters and Gaussian draws.
--
--   1. **Algorithm 2** (PrivateMultiply): $s_i=\sqrt{\operatorname{Tr}(V^\top M_iV)}$, $\tilde w_i=w_i\min\{1,\omega/s_i\}$ ($\tilde w_i=w_i$ if $s_i=0$), $Y=(\sum_i\tilde w_iM_i)V+\sigma G$.
--   2. **Algorithm 3** (PrivateScores): for $k=0,\dots,p$, a fresh sketch $Z_{k,0}$ with $\mathcal N(0,1/r)$ entries is pushed through $k$ replayed calls of Algorithm 2 with the stored weights $w^{(j)}$, radii $\omega_j$ and noise $\sigma_j=\kappa\omega_j/(32\sqrt{pdr\tau_{\max}})$; then $w^{(k+1)}_i=w^{(k)}_i\mathbf 1\{g^{(k)}_i\le\tau_{\max}\}$ with $g^{(k)}_i=\operatorname{Tr}(Z_{k,k}^\top M_iZ_{k,k})/\|Z_{k,k}\|_F^2$, and $\omega_{k+1}=2\sqrt{\tau_{\max}}\|Z_{k,k}\|_F$. The module also computes the run's $\Gamma_j$ of (14).
--   3. **Algorithm 4** (PrivateSoftFilter): with $w_i(t)=\bar w_i(1-\tau_i/\tau_{\max})^t$, $F(t)=\sum_iw_i(t)\tau_i$, $J=\lceil4\tau_{\max}/\kappa\rceil$ and noisy answers $z_t=F(t)+\xi_t$, $\xi_t\sim\mathcal N(0,\kappa^2/(50\log(2J/\beta)))$: the loop returns $w(t)$ for the first $t<J$ with $z_t\le\kappa/4$ (else $w(J)$); the binary search of the proof of Lemma 9 returns $\bar w$ if $z_0\le\kappa/4$ and otherwise $w(h)$ for the final $h$ of the search on $(0,J)$.
--   4. **Algorithm 1** (PrivateFastCovFilter): $\kappa=\Phi^{1/q}$, $r=\lceil C\log((n+d)/\beta)\rceil$, $\tau_{\min}=\kappa/(100\alpha)$, $\tau_{\max}=T(p+1)\kappa/(4\alpha)$, scores $\tau_i=g_i\mathbf 1\{\tau_{\min}<g_i\le\tau_{\max}\}$ from $Z=Z_{p,p}$, then the binary-search soft filter with $\beta/2$. Its transcript (32) consists of all sketches $Z_{k,j}$ and the queried pairs $(t,z_t)$.
--
--   **Formalization Note** Each query of $F(t)$ uses the draw indexed by $t$; the binary search queries distinct $t$, so every query has fresh noise. The transcript is encoded in a fixed space: an array of the $Z_{k,j}$ ($0$ for $j>k$) and $t\mapsto(1,z_t)$ for queried $t\in[0,J]$, $(0,0)$ otherwise; the query order is recovered from it. The constant $C$ of Line 3 is a parameter.
-- source:
--   Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, Efficient Private and Robust Statistics, STOC 2027 submission (manuscript sha256 1a69e17a…), Algorithm 1, p.16; Algorithm 2, p.17; Algorithm 3, p.18; Algorithm 4 and the proof of Lemma 9, pp.22–23; (14), p.19; (32), p.27

import Mathlib
import Definitions.Def_PrivRobustStat_Model

namespace PrivRobustStat

/-!
# The private covariance filter: Algorithms 2, 3, 4 and 1 as maps of data and Gaussian draws

Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, *Efficient Private and Robust Statistics*, STOC 2027
submission (manuscript sha256 1a69e17a…): Algorithm 1 (p.16), Algorithm 2 (p.17), Algorithm 3
(p.18), Algorithm 4 and the binary-search implementation in the proof of Lemma 9 (pp.22–23), the
transcript (32) (p.27).

**Formalization Note.**
* Each algorithm is a deterministic function of the private data, the public inputs and its
  Gaussian draws, which are coordinates of one standard Gaussian vector `g` (`stdGauss`); a draw from
  `N(0, s²)` is `s · g_i`. The dataset is `x[n]` with the public centre `c`, and
  `M_i := (x_i − c)(x_i − c)⊤` (p.15).
* Algorithm 3 uses `g (k, 0, a, b)/√r` for the entries of `Z_{k,0}` and `g (k, j, a, b)` (`j ≥ 1`)
  for the matrix `G` of the call `(k, j)` to Algorithm 2: fresh draws for every `Z_{k,0}` and every
  call. Indices `k, j` keep the paper's meaning (`k ∈ [0, p]`, `j ∈ [k]`).
* Algorithm 4 uses the draw `ξ t` for the query of `F(t)`. The loop queries `t = 0, 1, …` in order,
  the binary search queries distinct `t`, so each query gets a fresh draw, as in the paper.
* The loop form is written in closed form: it returns `w(t)` for the first `t ∈ [0, J − 1]` whose
  test passes, and `w(J)` if none does, where `w_i(t) := w̄_i(1 − τ_i/τ_max)^t` (proof of Lemma 9).
* The transcript (32) of a filtering call is encoded in a fixed measurable space: the sketches
  `Z_{k,j}` as an array indexed by `(k, j) ∈ [0, p]²` (entries with `j > k` are `0`), and the
  binary-search queries as `t ↦ (1, z_t)` for queried `t ∈ [0, J]` and `t ↦ (0, 0)` otherwise. The
  query order is a function of this encoding (the search is deterministic given its answers), and
  conversely, so the encoding carries exactly the information of the ordered transcript.
* Matrices are compared and multiplied as `Matrix`; outputs that a measure is put on are typed as
  `Fin d → Fin r → ℝ` (Mathlib has no measurable-space instance on `Matrix`).
-/

open Classical

/-- `Tr(Z⊤ N Z)`. -/
noncomputable def quadTr {d r : ℕ} (Z : Matrix (Fin d) (Fin r) ℝ) (N : Matrix (Fin d) (Fin d) ℝ) :
    ℝ :=
  Matrix.trace (Z.transpose * N * Z)

/-- The score `g := Tr(Z⊤ M Z)/‖Z‖²_F`, and `0` if `Z = 0` (Algorithm 1, Line 6; Algorithm 3,
Line 7). -/
noncomputable def score {d r : ℕ} (Z : Matrix (Fin d) (Fin r) ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    ℝ :=
  if Z = 0 then 0 else quadTr Z M / frob Z ^ 2

/-- Algorithm 2, `PrivateMultiply(M[n], w; V, ω, σ)` (p.17), with its Gaussian matrix `G`:
`s_i := √Tr(V⊤M_iV)`, `w̃_i := w_i min{1, ω/s_i}` (`w̃_i := w_i` when `s_i = 0`), and
`Y := (∑_i w̃_i M_i) V + σ G`. -/
noncomputable def privMultiply {d n r : ℕ} (x : Fin n → Vec d) (c : Vec d) (w : Fin n → ℝ)
    (V : Matrix (Fin d) (Fin r) ℝ) (ω σ : ℝ) (G : Matrix (Fin d) (Fin r) ℝ) :
    Matrix (Fin d) (Fin r) ℝ :=
  let s : Fin n → ℝ := fun i => Real.sqrt (quadTr V (outer (x i - c)))
  let wt : Fin n → ℝ := fun i => if s i = 0 then w i else w i * min 1 (ω / s i)
  (∑ i, wt i • outer (x i - c)) * V + σ • G

/-- The state of Algorithm 3 after some outer iterations: the stored weights `w^(j)` and clipping
radii `ω_j` (only `j` up to the current iteration are meaningful). -/
structure A3State (n : ℕ) where
  wt : ℕ → Fin n → ℝ
  om : ℕ → ℝ

/-- `σ_j := κω_j/(32√(p d r τ_max))` (Algorithm 3, Line 5). -/
noncomputable def sigmaJ (d r p : ℕ) (κ τmax ω : ℝ) : ℝ :=
  κ * ω / (32 * Real.sqrt ((p : ℝ) * d * r * τmax))

/-- The replayed sketches `Z_{k,0}, …, Z_{k,k}` of outer iteration `k` of Algorithm 3 (Lines 3–6),
given the stored weights and radii in `st`. -/
noncomputable def replay {d n r : ℕ} (x : Fin n → Vec d) (c : Vec d) (κ τmax : ℝ) (p : ℕ)
    (g : ℕ × ℕ × Fin d × Fin r → ℝ) (st : A3State n) (k : ℕ) : ℕ → Matrix (Fin d) (Fin r) ℝ
  | 0 => Matrix.of fun a b => (Real.sqrt r)⁻¹ * g (k, 0, a, b)
  | j + 1 =>
      privMultiply x c (st.wt (j + 1)) (replay x c κ τmax p g st k j) (st.om (j + 1))
        (sigmaJ d r p κ τmax (st.om (j + 1))) (Matrix.of fun a b => g (k, j + 1, a, b))

/-- One outer iteration `k` of Algorithm 3 (Lines 7–9): scores from `Z_{k,k}`, the hard cutoff
`w^(k+1)_i := w^(k)_i 1{g^(k)_i ≤ τ_max}`, and `ω_{k+1} := 2√τ_max ‖Z_{k,k}‖_F`. -/
noncomputable def a3step {d n r : ℕ} (x : Fin n → Vec d) (c : Vec d) (κ τmax : ℝ) (p : ℕ)
    (g : ℕ × ℕ × Fin d × Fin r → ℝ) (k : ℕ) (st : A3State n) : A3State n :=
  let Z := replay x c κ τmax p g st k k
  { wt := Function.update st.wt (k + 1)
      (fun i => if score Z (outer (x i - c)) ≤ τmax then st.wt k i else 0)
    om := Function.update st.om (k + 1) (2 * Real.sqrt τmax * frob Z) }

/-- The state of Algorithm 3 after outer iterations `0, …, k − 1`, starting from `w^(0) := w`. -/
noncomputable def a3state {d n r : ℕ} (x : Fin n → Vec d) (c : Vec d) (w : Fin n → ℝ)
    (κ τmax : ℝ) (p : ℕ) (g : ℕ × ℕ × Fin d × Fin r → ℝ) : ℕ → A3State n
  | 0 => ⟨fun _ => w, fun _ => 0⟩
  | k + 1 => a3step x c κ τmax p g k (a3state x c w κ τmax p g k)

/-- The sketch `Z_{k,j}` of Algorithm 3. -/
noncomputable def a3sketch {d n r : ℕ} (x : Fin n → Vec d) (c : Vec d) (w : Fin n → ℝ)
    (κ τmax : ℝ) (p : ℕ) (g : ℕ × ℕ × Fin d × Fin r → ℝ) (k j : ℕ) : Matrix (Fin d) (Fin r) ℝ :=
  replay x c κ τmax p g (a3state x c w κ τmax p g k) k j

/-- The output weights `w̄ := w^(p+1)` of Algorithm 3. -/
noncomputable def a3weights {d n r : ℕ} (x : Fin n → Vec d) (c : Vec d) (w : Fin n → ℝ)
    (κ τmax : ℝ) (p : ℕ) (g : ℕ × ℕ × Fin d × Fin r → ℝ) : Fin n → ℝ :=
  (a3state x c w κ τmax p g (p + 1)).wt (p + 1)

/-- The output sketch `Z := Z_{p,p}` of Algorithm 3. -/
noncomputable def a3Z {d n r : ℕ} (x : Fin n → Vec d) (c : Vec d) (w : Fin n → ℝ)
    (κ τmax : ℝ) (p : ℕ) (g : ℕ × ℕ × Fin d × Fin r → ℝ) : Matrix (Fin d) (Fin r) ℝ :=
  a3sketch x c w κ τmax p g p p

/-- The matrices `Γ_j` of (14) for a run of Algorithm 3: `Γ₀ := I`,
`Γ_j := Σ̂(w^(j)) Γ_{j−1} Σ̂(w^(j)) + rσ_j² I`, with `Σ̂(u) = ∑_i u_i M_i` and the run's own `w^(j)`
and `σ_j`. -/
noncomputable def a3Gamma {d n r : ℕ} (x : Fin n → Vec d) (c : Vec d) (w : Fin n → ℝ)
    (κ τmax : ℝ) (p : ℕ) (g : ℕ × ℕ × Fin d × Fin r → ℝ) (j : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  let st := a3state x c w κ τmax p g p
  gammaSeq (fun i => covC x (st.wt i) c)
    (fun i => (r : ℝ) * sigmaJ d r p κ τmax (st.om i) ^ 2) j

/-- The noise scale `σ_j` of call `j` in a run of Algorithm 3. -/
noncomputable def a3sigma {d n r : ℕ} (x : Fin n → Vec d) (c : Vec d) (w : Fin n → ℝ)
    (κ τmax : ℝ) (p : ℕ) (g : ℕ × ℕ × Fin d × Fin r → ℝ) (j : ℕ) : ℝ :=
  sigmaJ d r p κ τmax ((a3state x c w κ τmax p g p).om j)

/-- `w(t)_i := w̄_i (1 − τ_i/τ_max)^t` (proof of Lemma 9, p.22). -/
noncomputable def filtW {n : ℕ} (wbar τ : Fin n → ℝ) (τmax : ℝ) (t : ℕ) : Fin n → ℝ :=
  fun i => wbar i * (1 - τ i / τmax) ^ t

/-- `F(t) := ∑_i w_i(t) τ_i`. -/
noncomputable def Fval {n : ℕ} (wbar τ : Fin n → ℝ) (τmax : ℝ) (t : ℕ) : ℝ :=
  ∑ i, filtW wbar τ τmax t i * τ i

/-- `J := ⌈4τ_max/κ⌉` (Algorithm 4, Line 1). -/
noncomputable def Jcount (κ τmax : ℝ) : ℕ := ⌈4 * τmax / κ⌉₊

/-- The standard deviation `κ/√(50ζ)` of `ξ_t ∼ N(0, κ²/(50ζ))`, with `ζ := log(2J/β)`. -/
noncomputable def softSd (κ τmax β : ℝ) : ℝ :=
  κ / Real.sqrt (50 * Real.log (2 * (Jcount κ τmax : ℝ) / β))

/-- The noisy answer `z_t := F(t) + ξ_t` to the query of `F(t)` (Algorithm 4, Line 3). -/
noncomputable def zAns {n : ℕ} (wbar τ : Fin n → ℝ) (κ τmax β : ℝ) (ξ : ℕ → ℝ) (t : ℕ) : ℝ :=
  Fval wbar τ τmax t + softSd κ τmax β * ξ t

/-- Algorithm 4, `PrivateSoftFilter(w̄; τ[n], κ, τ_max, β)` (p.22), as printed (the loop over
`t ∈ [0, J − 1]`). -/
noncomputable def softFilterLoop {n : ℕ} (wbar τ : Fin n → ℝ) (κ τmax β : ℝ) (ξ : ℕ → ℝ) :
    Fin n → ℝ :=
  let S := (Finset.range (Jcount κ τmax)).filter fun t => zAns wbar τ κ τmax β ξ t ≤ κ / 4
  if h : S.Nonempty then filtW wbar τ τmax (S.min' h) else filtW wbar τ τmax (Jcount κ τmax)

/-- Step (3) of the binary search (proof of Lemma 9, p.23): while `h > l + 1`, query
`t := ⌊(l + h)/2⌋`; if `z_t > thr` set `l ← t`, else `h ← t`. Returns the final `h`. -/
noncomputable def bsearch (z : ℕ → ℝ) (thr : ℝ) (l h : ℕ) : ℕ :=
  if hlt : l + 1 < h then
    if thr < z ((l + h) / 2) then bsearch z thr ((l + h) / 2) h else bsearch z thr l ((l + h) / 2)
  else h
termination_by h - l
decreasing_by all_goals omega

/-- The indices `t` queried in step (3) of the binary search. -/
noncomputable def bsearchQueries (z : ℕ → ℝ) (thr : ℝ) (l h : ℕ) : Finset ℕ :=
  if hlt : l + 1 < h then
    insert ((l + h) / 2)
      (if thr < z ((l + h) / 2) then bsearchQueries z thr ((l + h) / 2) h
        else bsearchQueries z thr l ((l + h) / 2))
  else ∅
termination_by h - l
decreasing_by all_goals omega

/-- Algorithm 4 implemented by the binary search of the proof of Lemma 9 (p.23): (1) query `F(0)`;
if `z_0 ≤ κ/4` return `w̄`; (2)–(3) binary search on `(l, h) := (0, J)`; (4) return `w(h)`. -/
noncomputable def softFilterBin {n : ℕ} (wbar τ : Fin n → ℝ) (κ τmax β : ℝ) (ξ : ℕ → ℝ) :
    Fin n → ℝ :=
  if zAns wbar τ κ τmax β ξ 0 ≤ κ / 4 then wbar
  else filtW wbar τ τmax (bsearch (zAns wbar τ κ τmax β ξ) (κ / 4) 0 (Jcount κ τmax))

/-- The set of indices `t` queried by the binary-search implementation of Algorithm 4. -/
noncomputable def softQueries {n : ℕ} (wbar τ : Fin n → ℝ) (κ τmax β : ℝ) (ξ : ℕ → ℝ) :
    Finset ℕ :=
  if zAns wbar τ κ τmax β ξ 0 ≤ κ / 4 then {0}
  else insert 0 (bsearchQueries (zAns wbar τ κ τmax β ξ) (κ / 4) 0 (Jcount κ τmax))

/-- The transcript `{(t, z_t)}` of the binary search, encoded as `t ↦ (1, z_t)` for queried
`t ∈ [0, J]` and `t ↦ (0, 0)` otherwise. -/
noncomputable def softTranscript {n : ℕ} (wbar τ : Fin n → ℝ) (κ τmax β : ℝ) (ξ : ℕ → ℝ) :
    Fin (Jcount κ τmax + 1) → ℝ × ℝ :=
  fun t => if (t : ℕ) ∈ softQueries wbar τ κ τmax β ξ then (1, zAns wbar τ κ τmax β ξ t) else (0, 0)

/-- The sketch dimension `r := ⌈C log((n + d)/β)⌉` of Algorithm 1, Line 3, with the constant `C`
as a parameter. -/
noncomputable def rDim (C : ℝ) (n d : ℕ) (β : ℝ) : ℕ := ⌈C * Real.log (((n : ℝ) + d) / β)⌉₊

/-- `κ := Φ^{1/q}` (Algorithm 1, Line 2). -/
noncomputable def kappaOf (d : ℕ) (Φ : ℝ) : ℝ := Φ ^ ((1 : ℝ) / (qExp d : ℝ))

/-- `τ_min := κ/(100α)` (Algorithm 1, Line 4). -/
noncomputable def tauMin (d : ℕ) (Φ α : ℝ) : ℝ := kappaOf d Φ / (100 * α)

/-- `τ_max := T(p + 1)κ/(4α)` (Algorithm 1, Line 4). -/
noncomputable def tauMax (d : ℕ) (Φ : ℝ) (T : ℕ) (α : ℝ) : ℝ :=
  (T : ℝ) * ((pDepth d : ℝ) + 1) * kappaOf d Φ / (4 * α)

/-- The Gaussian draws of one filtering call: Algorithm 3's (`inl`) and Algorithm 4's (`inr`). -/
abbrev A1Idx (d r : ℕ) := (ℕ × ℕ × Fin d × Fin r) ⊕ ℕ

/-- The scores `τ_i := g_i 1{τ_min < g_i ≤ τ_max}` with `g_i := Tr(Z⊤M_iZ)/‖Z‖²_F` (Algorithm 1,
Lines 6–7). -/
noncomputable def a1tau {d n : ℕ} (C : ℝ) (x : Fin n → Vec d) (c : Vec d) (w : Fin n → ℝ) (Φ : ℝ)
    (T : ℕ) (α β : ℝ) (g : A1Idx d (rDim C n d β) → ℝ) : Fin n → ℝ :=
  fun i =>
    let gi := score (a3Z x c w (kappaOf d Φ) (tauMax d Φ T α) (pDepth d) (fun a => g (Sum.inl a)))
      (outer (x i - c))
    if tauMin d Φ α < gi ∧ gi ≤ tauMax d Φ T α then gi else 0

/-- The output weights `w̄` of Algorithm 3 inside Algorithm 1 (Line 5). -/
noncomputable def a1wbar {d n : ℕ} (C : ℝ) (x : Fin n → Vec d) (c : Vec d) (w : Fin n → ℝ)
    (Φ : ℝ) (T : ℕ) (α β : ℝ) (g : A1Idx d (rDim C n d β) → ℝ) : Fin n → ℝ :=
  a3weights x c w (kappaOf d Φ) (tauMax d Φ T α) (pDepth d) (fun a => g (Sum.inl a))

/-- Algorithm 1, `PrivateFastCovFilter(M[n], w; Φ, T, α, β)` (p.16), with Algorithm 4 implemented by
the binary search (Line 8, `PrivateSoftFilter(w̄, τ[n]; κ, τ_max, β/2)`). Output: the weights `w′`. -/
noncomputable def alg1 {d n : ℕ} (C : ℝ) (x : Fin n → Vec d) (c : Vec d) (w : Fin n → ℝ) (Φ : ℝ)
    (T : ℕ) (α β : ℝ) (g : A1Idx d (rDim C n d β) → ℝ) : Fin n → ℝ :=
  softFilterBin (a1wbar C x c w Φ T α β g) (a1tau C x c w Φ T α β g) (kappaOf d Φ)
    (tauMax d Φ T α) (β / 2) (fun t => g (Sum.inr t))

/-- The transcript space of a filtering call: the sketches `Z_{k,j}`, `k, j ∈ [0, p]`, and the
encoded binary-search queries `t ∈ [0, J]`. -/
abbrev A1Transcript (d r p J : ℕ) :=
  (Fin (p + 1) → Fin (p + 1) → Fin d → Fin r → ℝ) × (Fin (J + 1) → ℝ × ℝ)

/-- The transcript (32) of one filtering call: all sketches `Z_{k,j}` (`j ≤ k`; `0` for `j > k`) of
Algorithm 3, and the queried pairs `(t, z_t)` of the binary search of Algorithm 4. -/
noncomputable def alg1Transcript {d n : ℕ} (C : ℝ) (x : Fin n → Vec d) (c : Vec d)
    (w : Fin n → ℝ) (Φ : ℝ) (T : ℕ) (α β : ℝ) (g : A1Idx d (rDim C n d β) → ℝ) :
    A1Transcript d (rDim C n d β) (pDepth d) (Jcount (kappaOf d Φ) (tauMax d Φ T α)) :=
  (fun k j => if (j : ℕ) ≤ k then
      fun a b => a3sketch x c w (kappaOf d Φ) (tauMax d Φ T α) (pDepth d) (fun a => g (Sum.inl a))
        k j a b
    else 0,
   softTranscript (a1wbar C x c w Φ T α β g) (a1tau C x c w Φ T α β g) (kappaOf d Φ)
    (tauMax d Φ T α) (β / 2) (fun t => g (Sum.inr t)))

end PrivRobustStat


