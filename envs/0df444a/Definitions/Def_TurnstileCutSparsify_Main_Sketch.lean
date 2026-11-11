-- Prove2me | Definitions.Def_TurnstileCutSparsify_Main_Sketch
-- name    : TurnstileCutSparsify_Main_Sketch
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:41:18.231196+00:00
-- url     : https://prove2.me/theorems/df1c2847-c4b0-41be-afea-f561d93bd578
-- title:
--   The three-table sketch: parameters (4), tables (7)–(9) and (34), the decoder (10)–(12) by pair enumeration or candidate discovery, and the analysis quantities (13)–(16)
-- statement:
--   **Parameters (4).** $J=\lceil\log_2(8n^4U)\rceil$, $\ell=\lceil\ln(64n^2J/\delta)\rceil$, $\beta=\lceil C_\beta J\ell/\varepsilon^2\rceil$; $R$ is the smallest odd integer $\ge C_R\ell$, $B$ the smallest power of two $\ge C_B\beta$, $d=\lceil\log_2N\rceil$ and $B_S$ the smallest power of two $\ge C_B\beta(d+1)$, for absolute constants $C_B,C_R,C_\beta$.
--
--   **Tables (§3.2).** Survival bits $\xi_{e,a}$ ($a\in[J]$) give $I_{e,k}=\prod_{a=1}^k\xi_{e,a}$, $I_{e,0}=1$. With the signed incidence vectors $\chi_v(e)=x_e$ if $v=\min e$, $-x_e$ if $v=\max e$, $0$ otherwise, every vertex $v$ keeps, at every layer $k\in\{0,\dots,J\}$ and row $r\in[R]$,
--   $S^{k,r}(v,b)=\sum_{h_S^{k,r}(e)=b}\chi_v(e)I_{e,k}s^{k,r}_e$ (7), the bit counters $S^{k,r}_j(v,b)$ with the extra factor $(-1)^{\mathrm{bit}_j(\mathrm{id}(e))}$ (34), $D^{k,r,p,i}(v,b)=\sum_{h_T^{k,r}(e)=b}\chi_v(e)I_{e,k}\rho^{k,r,p,i}_e$ (8) for $p\in[32R]$, $i\in\{1,2\}$, and $T^{k,r,l}(v,b)=\sum_{h_T^{k,r}(e)=b}\chi_v(e)I_{e,k}\sigma^{k,r,l}_e$ (9). A counter on a vertex set is the sum over its vertices.
--
--   **Decoder (§3.3).** With the query cuts of a forest: $y_e(k)=\mathrm{median}_r\,\mathrm{sgn}_e s^{k,r}_eS^{k,r}(S_e,h_S^{k,r}(e))$, $\theta_e(k)=\max\{1/2,t_e(k)/4\}$, $\hat j_e=\min\{0\le k\le J:y_e(k)\ge\theta_e(k)\}$ (10); $E^\star$ = candidates with finite $\hat j_e$, abort if $|E^\star|>\lceil8n\beta\rceil$; difference queries $Y^{r,p}_e$, $\psi_r(e)$ = median over groups of the mean of 32 squared difference queries, $r_e=\arg\min_r\psi_r(e)$ (11); $\hat w_e=\frac1R\sum_l\mathrm{sgn}_e\sigma^{k,r_e,l}_eT^{k,r_e,l}(S_e,h_T^{k,r_e}(e))$, $Z_e=2^k\hat w_e$ (12); return $H=(E^\star,Z)$, aborting if some $Z_e\le0$. **Pair enumeration** tests every eligible pair; **candidate discovery** (§7.1) tests the eligible pairs whose identifier $\hat m=\sum_j1[S^{k,r}_j(S_q,b)S^{k,r}(S_q,b)<0]2^j$ is decoded from a nonzero selection bucket of some fundamental cut.
--
--   **Analysis (§4).** The load bound (13) $\sum_{f\in E(S_e,V\setminus S_e)}\min\{x_f/t_e(k),1\}I_{f,k}\le2.5\beta$; selection success (14) $|y_e(k)-x_eI_{e,k}|\le t_e(k)/24$; the baseline layer $k_e=\min\{k\ge0:x_e\ge5t_e(k)/24\}$ (15); $y^+_e(k)=y_e(k)+x_e(1-I_{e,k})$, $\eta_e=1[y^+_e(k_e)<\theta_e(k_e)]$, $j_e=k_e+\eta_e$ (16); the collision vector $v^{k,r}_e(f)=\mathrm{sgn}_e\,\mathrm{sgn}_{S_e}(f)x_fI_{f,k}1[h_T^{k,r}(f)=h_T^{k,r}(e)]$ ($f\ne e$), $v_e=v^{j_e,r_e}_e$.
--
--   **Copies (§7.3–7.4).** A copy's seeds are the A.4 seeds of all its hash and four-wise sign families and the seeds of its survival and evaluation tapes; its tables are those of the sketch with these coins.
--
--   **Formalization Note** `SketchParams` holds `n, U, ε, δ, C_B, C_R, C_β`; `Sketch` adds the selection width `2^b` and the integer vector `x`; `Setup` adds the forest `F` and the path-edge choice `q`. Layers are naturals `k ≤ J` (`lay k` clamps for indexing), rows/repetitions/groups are `Fin R`, `P_g = {32g,…,32g+31}`, a sign is a bit (`sgnB true = −1`), the median is the middle entry of the sorted list, `row` takes the first minimizing row, `jhat` is `none` for $\infty$, `decode` returns `none` on abort. `TableRand` is all randomness of §§3–6; `CopySeeds`, `copyTables`, `copyResult` describe one copy with A.4 families and tapes `tξ`, `tσ`; `OutputMatches` says an output list is the decoder's graph (empty on abort).
-- source:
--   Lin, Mirrokni, Woodruff (2026), Near-Optimal Space and Time Cut Sparsification in Turnstile Streams, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), §3.1 (4) and Table 2 pp. 12–13, §3.2 (7)–(9) pp. 13–14, §3.3 (10)–(12) pp. 14–15, (13)–(16) pp. 16–18, §4.3 p. 18, §7.1 (34) pp. 26–27, §7.3–7.4 pp. 31–37

import Mathlib
import Definitions.Def_TurnstileCutSparsify_Main_Graph
import Definitions.Def_TurnstileCutSparsify_Main_Streaming
import Definitions.Def_TurnstileCutSparsify_Main_Forest
import Definitions.Def_TurnstileCutSparsify_Main_Randomness

open scoped BigOperators Classical

noncomputable section

namespace TurnstileCutSparsify.Main

open TurnstileRank.TightBounds.RAM

/-!
# The three-table sketch, its recovery decoder, and the quantities of the analysis

Lin, Mirrokni, Woodruff, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…),
§3.1 (4) and Table 2 pp. 12–13, §3.2 (7)–(9) pp. 13–14, §3.3 (10)–(12) pp. 14–15, §4 (13)–(16)
pp. 16–18, §4.3 p. 18, §7.1 (34) pp. 26–27, §7.3–7.4 pp. 31–37.

**Parameters (4).** For `n, U, ε, δ` and the absolute constants `C_B, C_R, C_β`:
`J = ⌈log₂(8n⁴U)⌉`, `ℓ = ⌈ln(64 n² J / δ)⌉`, `β = ⌈C_β J ℓ / ε²⌉`, `R` the smallest odd integer
`≥ C_R ℓ`, `B = 2^{bB}` the smallest power of two `≥ C_B β`, `N = C(n, 2)`, `d = ⌈log₂ N⌉`, and
`B_S = 2^{bBS}` the smallest power of two `≥ C_B β (d + 1)`.

**Randomness.** Survival bits `ξ_{e,a}` (`a ∈ [J]`, here `Fin J`), so `I_{e,k} = Π_{a ≤ k} ξ_{e,a}`
and `I_{e,0} = 1`; selection hashes `h_S^{k,r}` into `2^{bSel}` buckets and selection signs
`s^{k,r}_e` (`SelCoins`); estimation hashes `h_T^{k,r}` into `B` buckets and diagnostic signs
`ρ^{k,r,p,i}_e`, `p ∈ [32R]`, `i ∈ {1, 2}` (`DiagCoins`); evaluation signs `σ^{k,r,l}_e`, `l ∈ [R]`
(`EvalSigns`). A sign is a bit (`true` is `−1`). Layers `k ∈ {0, …, J}` and rows, repetitions,
groups are indexed from `0`. `SelCoins.ofSeeds FH FS` draws `h_S^{k,r}` and `s^{k,r}` from the
seeded families `FH`, `FS` with one seed per layer and row (independent seeds for distinct
functions); likewise `DiagCoins.ofSeeds` with one seed per diagnostic sign family `(k, r, p, i)`.

**A sketch** (`Sketch`) is a parameter set `P`, a selection width `2^b` (`b = bB` in §§3–6, `b = bBS`
from §7.1 on) and the sketched integer vector `x` (the final graph `w`, or `W_i` in §7.3). Its
vertex counters are (7), (34), (8), (9) with the signed incidence vectors `χ_v(e) = x_e` if
`v = min e`, `−x_e` if `v = max e`, `0` otherwise; a counter on a vertex set `T` is the sum of the
vertex counters over `v ∈ T`.

**A setup** (`Setup`) adds the query forest `F` and the choice `q` of a minimum-weight path edge
for every eligible pair, which give `S_e`, `κ_e`, `sgn_e = sgn_{S_e}(e)` and the scale
`t_e(k) = 2^{−k} κ_e / β` (5).

**The decoder (§3.3).** `y_e(k)` is the median over rows of `sgn_e s^{k,r}_e S^{k,r}(S_e, h_S^{k,r}(e))`;
`θ_e(k) = max {1/2, t_e(k)/4}`; `ĵ_e` the first layer `k ≤ J` with `y_e(k) ≥ θ_e(k)` (`none` = `∞`).
For a candidate set, `E⋆` is the set of candidates with finite `ĵ_e`; the decoder aborts (`none`)
if `|E⋆| > ⌈8nβ⌉`. At `k = ĵ_e`, the difference queries
`Y^{r,p}_e = (sgn_e/2)(ρ^{k,r,p,1}_e D^{k,r,p,1}(S_e, b) − ρ^{k,r,p,2}_e D^{k,r,p,2}(S_e, b))`, `b = h_T^{k,r}(e)`,
give `ψ_r(e)`, the median over the `R` groups `P_g = {32g, …, 32g + 31}` of the mean of the 32
squared difference queries; `r_e` is the first row minimizing `ψ_r(e)` (ties to the smaller row).
`ŵ_e = (1/R) Σ_l sgn_e σ^{k,r_e,l}_e T^{k,r_e,l}(S_e, h_T^{k,r_e}(e))`, `Z_e = 2^k ŵ_e`, and the
output is `H = (E⋆, Z)`, aborting if some `Z_e ≤ 0`. A median of `R` values is the middle entry
(index `⌊R/2⌋`) of the sorted list. **Pair enumeration** uses the eligible pairs as candidates;
**candidate discovery** (§7.1) uses the eligible pairs `e` such that some fundamental cut `S_q`,
layer, row and bucket with nonzero base selection counter decodes to
`m̂ = Σ_{j<d} 1[S_j^{k,r}(S_q, b) S^{k,r}(S_q, b) < 0] 2^j = id(e)`.

**Analysis quantities.** The load bound (13), selection success (14), the baseline layer
`k_e = min {k ≥ 0 : x_e ≥ 5 t_e(k)/24}` (15), the hypothetical query
`y⁺_e(k) = y_e(k) + x_e (1 − I_{e,k})`, `η_e = 1[y⁺_e(k_e) < θ_e(k_e)]`, `j_e = k_e + η_e` (16), the
collision vectors `v^{k,r}_e` and `v_e = v^{j_e, r_e}_e` of §4.3.

`Tables P b` is the content of the three tables (with bit counters) of one copy, and `CopySeeds`
the seeds of one copy of §7.3–7.4: the Appendix A.4 seeds of every hash and four-wise sign family,
and the seeds of the survival and evaluation tapes.
-/

/-- The inputs `n, U, ε, δ` of the sketch and the absolute constants `C_B, C_R, C_β` of (4). -/
structure SketchParams where
  n : ℕ
  U : ℕ
  ε : ℝ
  δ : ℝ
  CB : ℝ
  CR : ℝ
  Cβ : ℝ

namespace SketchParams

variable (P : SketchParams)

/-- `N = C(n, 2)`. -/
def N : ℕ := P.n.choose 2
/-- `J = ⌈log₂(8 n⁴ U)⌉`. -/
def J : ℕ := Nat.clog 2 (8 * P.n ^ 4 * P.U)
/-- `ℓ = ⌈ln(64 n² J / δ)⌉`. -/
def ell : ℕ := ⌈Real.log (64 * (P.n : ℝ) ^ 2 * P.J / P.δ)⌉₊
/-- `β = ⌈C_β J ℓ / ε²⌉`. -/
def β : ℕ := ⌈P.Cβ * P.J * P.ell / P.ε ^ 2⌉₊
/-- `R`: the smallest odd integer `≥ C_R ℓ`. -/
def R : ℕ := if ⌈P.CR * P.ell⌉₊ % 2 = 1 then ⌈P.CR * P.ell⌉₊ else ⌈P.CR * P.ell⌉₊ + 1
/-- `log₂ B`: `B` is the smallest power of two `≥ C_B β`. -/
def bB : ℕ := Nat.clog 2 ⌈P.CB * P.β⌉₊
/-- `B = 2^{bB}`. -/
def B : ℕ := 2 ^ P.bB
/-- `d = ⌈log₂ N⌉`. -/
def d : ℕ := Nat.clog 2 P.N
/-- `log₂ B_S`: `B_S` is the smallest power of two `≥ C_B β (d + 1)`. -/
def bBS : ℕ := Nat.clog 2 ⌈P.CB * P.β * (P.d + 1)⌉₊
/-- `B_S = 2^{bBS}`. -/
def BS : ℕ := 2 ^ P.bBS

end SketchParams

/-- Survival bits `ξ_{e,a}`, `a ∈ [J]`. -/
abbrev SurvBits (n J : ℕ) := Pair n → Fin J → Bool

/-- Selection hashes into `2^b` buckets and selection signs, per layer and row. -/
structure SelCoins (n J R b : ℕ) where
  hS : Fin (J + 1) → Fin R → Pair n → Fin (2 ^ b)
  sS : Fin (J + 1) → Fin R → Pair n → Bool

/-- Estimation hashes into `2^b` buckets and diagnostic signs, per layer and row. -/
structure DiagCoins (n J R b : ℕ) where
  hT : Fin (J + 1) → Fin R → Pair n → Fin (2 ^ b)
  ρ : Fin (J + 1) → Fin R → Fin (32 * R) → Fin 2 → Pair n → Bool

/-- Evaluation signs `σ^{k,r,l}_e`. -/
abbrev EvalSigns (n J R : ℕ) := Fin (J + 1) → Fin R → Fin R → Pair n → Bool

set_option synthInstance.maxSize 1024 in
/-- The finitely many evaluation-sign assignments. -/
noncomputable instance (n J R : ℕ) : Fintype (EvalSigns n J R) := by
  unfold EvalSigns; infer_instance

/-- All the randomness of the three tables of §§3–6: survival bits, the seeds of the selection
hashes and signs, of the estimation hashes and diagnostic signs, and the evaluation signs. -/
abbrev TableRand (n J R : ℕ) (HS SS TS DS : Type*) :=
  SurvBits n J × ((Fin (J + 1) → Fin R → HS) × (Fin (J + 1) → Fin R → SS)) ×
    ((Fin (J + 1) → Fin R → TS) × (Fin (J + 1) → Fin R → Fin (32 * R) → Fin 2 → DS)) ×
    EvalSigns n J R

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- The finitely many outcomes of the randomness of the three tables. -/
noncomputable instance (n J R : ℕ) (HS SS TS DS : Type*) [Fintype HS] [Fintype SS] [Fintype TS]
    [Fintype DS] : Fintype (TableRand n J R HS SS TS DS) := by
  unfold TableRand SurvBits; infer_instance

/-- Selection coins drawn from seeded families, one independent seed per layer and row. -/
def SelCoins.ofSeeds {n J R b : ℕ} {HS SS : Type*} (FH : HS → Pair n → Fin (2 ^ b))
    (FS : SS → Pair n → Bool) (s : (Fin (J + 1) → Fin R → HS) × (Fin (J + 1) → Fin R → SS)) :
    SelCoins n J R b :=
  ⟨fun k r => FH (s.1 k r), fun k r => FS (s.2 k r)⟩

/-- Estimation hashes and diagnostic signs drawn from seeded families, one independent seed per
function. -/
def DiagCoins.ofSeeds {n J R b : ℕ} {TS DS : Type*} (FT : TS → Pair n → Fin (2 ^ b))
    (FD : DS → Pair n → Bool)
    (s : (Fin (J + 1) → Fin R → TS) × (Fin (J + 1) → Fin R → Fin (32 * R) → Fin 2 → DS)) :
    DiagCoins n J R b :=
  ⟨fun k r => FT (s.1 k r), fun k r p i => FD (s.2 k r p i)⟩

/-- `sgn_T(e) = 1[min e ∈ T] − 1[max e ∈ T]`. -/
def sgnS {n : ℕ} (T : Finset (Fin n)) (e : Pair n) : ℤ :=
  (if e.lo ∈ T then 1 else 0) - (if e.hi ∈ T then 1 else 0)

/-- The sum of vertex counters over a vertex set. -/
def onSet {n : ℕ} (f : Fin n → ℤ) (T : Finset (Fin n)) : ℤ := ∑ v ∈ T, f v

/-- The median of `m` reals: the middle entry of the sorted list. -/
def median {m : ℕ} (f : Fin m → ℝ) : ℝ :=
  ((List.ofFn f).mergeSort fun a b => decide (a ≤ b)).getD (m / 2) 0

/-- The Euclidean norm of a vector on the pairs. -/
def l2 {n : ℕ} (v : Pair n → ℝ) : ℝ := Real.sqrt (∑ f, v f ^ 2)

/-- One copy of the three-table sketch: parameters, selection width `2^b`, sketched vector `x`. -/
structure Sketch where
  P : SketchParams
  b : ℕ
  x : Pair P.n → ℤ

namespace Sketch

variable (K : Sketch)

/-- The layer index `k` as an element of `{0, …, J}` (every use has `k ≤ J`). -/
def lay (k : ℕ) : Fin (K.P.J + 1) := ⟨min k K.P.J, by omega⟩

/-- The survival indicator `I_{e,k} = Π_{a=1}^{k} ξ_{e,a}` (`I_{e,0} = 1`; `0` past layer `J`). -/
def surv (ξ : SurvBits K.P.n K.P.J) (e : Pair K.P.n) (k : ℕ) : ℤ :=
  if k ≤ K.P.J ∧ ∀ a : Fin K.P.J, a.val < k → ξ e a = true then 1 else 0

/-- The signed incidence vector `χ_v(e)`. -/
def chi (v : Fin K.P.n) (e : Pair K.P.n) : ℤ :=
  if v = e.lo then K.x e else if v = e.hi then -K.x e else 0

/-- The selection counter `S^{k,r}(v, b)` (7). -/
def selCtr (ξ : SurvBits K.P.n K.P.J) (sc : SelCoins K.P.n K.P.J K.P.R K.b) (k : ℕ)
    (r : Fin K.P.R) (v : Fin K.P.n) (bk : Fin (2 ^ K.b)) : ℤ :=
  ∑ e, if sc.hS (K.lay k) r e = bk then K.chi v e * K.surv ξ e k * sgnB (sc.sS (K.lay k) r e)
    else 0

/-- The bit counter `S_j^{k,r}(v, b)` (34). -/
def bitCtr (ξ : SurvBits K.P.n K.P.J) (sc : SelCoins K.P.n K.P.J K.P.R K.b) (k : ℕ)
    (r : Fin K.P.R) (j : ℕ) (v : Fin K.P.n) (bk : Fin (2 ^ K.b)) : ℤ :=
  ∑ e, if sc.hS (K.lay k) r e = bk then
      K.chi v e * K.surv ξ e k * sgnB (sc.sS (K.lay k) r e) * sgnB ((pairId e).testBit j)
    else 0

/-- The diagnostic counter `D^{k,r,p,i}(v, b)` (8). -/
def diagCtr (ξ : SurvBits K.P.n K.P.J) (dc : DiagCoins K.P.n K.P.J K.P.R K.P.bB) (k : ℕ)
    (r : Fin K.P.R) (p : Fin (32 * K.P.R)) (i : Fin 2) (v : Fin K.P.n) (bk : Fin (2 ^ K.P.bB)) :
    ℤ :=
  ∑ e, if dc.hT (K.lay k) r e = bk then K.chi v e * K.surv ξ e k * sgnB (dc.ρ (K.lay k) r p i e)
    else 0

/-- The estimation counter `T^{k,r,l}(v, b)` (9). -/
def estCtr (ξ : SurvBits K.P.n K.P.J) (dc : DiagCoins K.P.n K.P.J K.P.R K.P.bB)
    (σ : EvalSigns K.P.n K.P.J K.P.R) (k : ℕ) (r l : Fin K.P.R) (v : Fin K.P.n)
    (bk : Fin (2 ^ K.P.bB)) : ℤ :=
  ∑ e, if dc.hT (K.lay k) r e = bk then K.chi v e * K.surv ξ e k * sgnB (σ (K.lay k) r l e)
    else 0

/-- The real weights `x_e`. -/
def xr (e : Pair K.P.n) : ℝ := (K.x e : ℝ)

end Sketch

/-- The content of the three tables of one copy (with `d` bit counters per selection bucket). -/
structure Tables (P : SketchParams) (b : ℕ) where
  sel : Fin P.n → Fin (P.J + 1) → Fin P.R → Fin (2 ^ b) → ℤ
  bits : Fin P.n → Fin (P.J + 1) → Fin P.R → Fin P.d → Fin (2 ^ b) → ℤ
  diag : Fin P.n → Fin (P.J + 1) → Fin P.R → Fin (32 * P.R) → Fin 2 → Fin (2 ^ P.bB) → ℤ
  est : Fin P.n → Fin (P.J + 1) → Fin P.R → Fin P.R → Fin (2 ^ P.bB) → ℤ

/-- The tables of the sketch `K` for the given randomness. -/
def Sketch.tables (K : Sketch) (ξ : SurvBits K.P.n K.P.J) (sc : SelCoins K.P.n K.P.J K.P.R K.b)
    (dc : DiagCoins K.P.n K.P.J K.P.R K.P.bB) (σ : EvalSigns K.P.n K.P.J K.P.R) : Tables K.P K.b :=
  ⟨fun v k r bk => K.selCtr ξ sc k r v bk, fun v k r j bk => K.bitCtr ξ sc k r j v bk,
    fun v k r p i bk => K.diagCtr ξ dc k r p i v bk,
    fun v k r l bk => K.estCtr ξ dc σ k r l v bk⟩

/-- A sketch together with its query forest and the choice of a minimum-weight path edge. -/
structure Setup extends Sketch where
  F : RootedForest P.n
  q : Pair P.n → Fin P.n

namespace Setup

variable (S : Setup)

/-- The query cut `S_e`. -/
def Se (e : Pair S.P.n) : Finset (Fin S.P.n) := qCut S.F S.q e
/-- The query weight `κ_e`. -/
def κ (e : Pair S.P.n) : ℝ := qWeight S.F S.q e
/-- `sgn_e = sgn_{S_e}(e)`. -/
def sgnE (e : Pair S.P.n) : ℤ := sgnS (S.Se e) e
/-- The scale `t_e(k) = 2^{−k} κ_e / β` (5). -/
def t (e : Pair S.P.n) (k : ℕ) : ℝ := S.κ e / ((2 : ℝ) ^ k * S.P.β)
/-- The threshold `θ_e(k) = max {1/2, t_e(k)/4}` (10). -/
def θ (e : Pair S.P.n) (k : ℕ) : ℝ := max (1 / 2) (S.t e k / 4)

/-- The selection query `y_e(k)`. -/
def y (ξ : SurvBits S.P.n S.P.J) (sc : SelCoins S.P.n S.P.J S.P.R S.b) (e : Pair S.P.n)
    (k : ℕ) : ℝ :=
  median fun r : Fin S.P.R =>
    ((S.sgnE e * sgnB (sc.sS (S.lay k) r e) *
      onSet (fun v => S.selCtr ξ sc k r v (sc.hS (S.lay k) r e)) (S.Se e) : ℤ) : ℝ)

/-- The selected layer `ĵ_e` (10): the first `k ≤ J` with `y_e(k) ≥ θ_e(k)`. -/
def jhat (ξ : SurvBits S.P.n S.P.J) (sc : SelCoins S.P.n S.P.J S.P.R S.b) (e : Pair S.P.n) :
    Option ℕ :=
  (List.range (S.P.J + 1)).find? fun k => decide (S.θ e k ≤ S.y ξ sc e k)

/-- The difference query `Y^{r,p}_e` at layer `k`. -/
def Ydiff (ξ : SurvBits S.P.n S.P.J) (dc : DiagCoins S.P.n S.P.J S.P.R S.P.bB) (e : Pair S.P.n)
    (k : ℕ) (r : Fin S.P.R) (p : Fin (32 * S.P.R)) : ℝ :=
  (S.sgnE e : ℝ) / 2 *
    (((sgnB (dc.ρ (S.lay k) r p 0 e) *
        onSet (fun v => S.diagCtr ξ dc k r p 0 v (dc.hT (S.lay k) r e)) (S.Se e) : ℤ) : ℝ) -
      ((sgnB (dc.ρ (S.lay k) r p 1 e) *
        onSet (fun v => S.diagCtr ξ dc k r p 1 v (dc.hT (S.lay k) r e)) (S.Se e) : ℤ) : ℝ))

/-- The diagnostic `ψ_r(e)` (11) at layer `k`. -/
def ψ (ξ : SurvBits S.P.n S.P.J) (dc : DiagCoins S.P.n S.P.J S.P.R S.P.bB) (e : Pair S.P.n)
    (k : ℕ) (r : Fin S.P.R) : ℝ :=
  median fun g : Fin S.P.R =>
    (1 / 32 : ℝ) * ∑ i : Fin 32, (S.Ydiff ξ dc e k r ⟨32 * g.val + i.val, by omega⟩) ^ 2

/-- The chosen row `r_e` (11): the first row minimizing `ψ_r(e)`. -/
def row (ξ : SurvBits S.P.n S.P.J) (dc : DiagCoins S.P.n S.P.J S.P.R S.P.bB) (e : Pair S.P.n)
    (k : ℕ) : Option (Fin S.P.R) :=
  (List.finRange S.P.R).argmin (S.ψ ξ dc e k)

/-- The weight estimate `ŵ_e` (12) at layer `k` and row `r`. -/
def what (ξ : SurvBits S.P.n S.P.J) (dc : DiagCoins S.P.n S.P.J S.P.R S.P.bB)
    (σ : EvalSigns S.P.n S.P.J S.P.R) (e : Pair S.P.n) (k : ℕ) (r : Fin S.P.R) : ℝ :=
  (1 / (S.P.R : ℝ)) * ∑ l : Fin S.P.R,
    ((S.sgnE e * sgnB (σ (S.lay k) r l e) *
      onSet (fun v => S.estCtr ξ dc σ k r l v (dc.hT (S.lay k) r e)) (S.Se e) : ℤ) : ℝ)

/-- The output weight `Z_e = 2^{ĵ_e} ŵ_e` of a selected pair (`0` if `ĵ_e = ∞`). -/
def outW (ξ : SurvBits S.P.n S.P.J) (sc : SelCoins S.P.n S.P.J S.P.R S.b)
    (dc : DiagCoins S.P.n S.P.J S.P.R S.P.bB) (σ : EvalSigns S.P.n S.P.J S.P.R)
    (e : Pair S.P.n) : ℝ :=
  match S.jhat ξ sc e with
  | none => 0
  | some k => match S.row ξ dc e k with
    | none => 0
    | some r => (2 : ℝ) ^ k * S.what ξ dc σ e k r

/-- The selected set `E⋆` among the candidates. -/
def selected (ξ : SurvBits S.P.n S.P.J) (sc : SelCoins S.P.n S.P.J S.P.R S.b)
    (cands : Finset (Pair S.P.n)) : Finset (Pair S.P.n) :=
  cands.filter fun e => (S.jhat ξ sc e).isSome

/-- The decoder of §3.3 on a candidate set: abort if `|E⋆| > ⌈8nβ⌉` or some `Z_e ≤ 0`, else
return `H = (E⋆, Z)`. -/
def decode (ξ : SurvBits S.P.n S.P.J) (sc : SelCoins S.P.n S.P.J S.P.R S.b)
    (dc : DiagCoins S.P.n S.P.J S.P.R S.P.bB) (σ : EvalSigns S.P.n S.P.J S.P.R)
    (cands : Finset (Pair S.P.n)) : Option (Pair S.P.n → ℝ) :=
  if 8 * S.P.n * S.P.β < (S.selected ξ sc cands).card then none
  else if ∀ e ∈ S.selected ξ sc cands, 0 < S.outW ξ sc dc σ e then
    some fun e => if e ∈ S.selected ξ sc cands then S.outW ξ sc dc σ e else 0
  else none

/-- Pair enumeration: every eligible pair is a candidate. -/
def enumCands : Finset (Pair S.P.n) := Finset.univ.filter fun e => Eligible S.F e

/-- The identifier decoded from a selection bucket on the vertex set `T` (§7.1). -/
def decodedId (ξ : SurvBits S.P.n S.P.J) (sc : SelCoins S.P.n S.P.J S.P.R S.b)
    (T : Finset (Fin S.P.n)) (k : ℕ) (r : Fin S.P.R) (bk : Fin (2 ^ S.b)) : ℕ :=
  ∑ j ∈ Finset.range S.P.d,
    if onSet (fun v => S.bitCtr ξ sc k r j v bk) T * onSet (fun v => S.selCtr ξ sc k r v bk) T < 0
    then 2 ^ j else 0

/-- Candidate discovery (§7.1): the eligible pairs whose identifier is decoded from a nonzero
selection bucket of some fundamental cut, layer and row. -/
def discCands (ξ : SurvBits S.P.n S.P.J) (sc : SelCoins S.P.n S.P.J S.P.R S.b) :
    Finset (Pair S.P.n) :=
  Finset.univ.filter fun e => Eligible S.F e ∧
    ∃ (v : Fin S.P.n) (k : ℕ) (r : Fin S.P.R) (bk : Fin (2 ^ S.b)), k ≤ S.P.J ∧
      S.F.par v ≠ none ∧ onSet (fun u => S.selCtr ξ sc k r u bk) (S.F.fundCut v) ≠ 0 ∧
      S.decodedId ξ sc (S.F.fundCut v) k r bk = pairId e

/-- The load bound (13) for every eligible pair and layer. -/
def LoadOK (ξ : SurvBits S.P.n S.P.J) : Prop :=
  ∀ e, Eligible S.F e → ∀ k ≤ S.P.J,
    ∑ f ∈ cutEdges S.xr (S.Se e), min (S.xr f / S.t e k) 1 * (S.surv ξ f k : ℝ) ≤ 2.5 * S.P.β

/-- Selection success (14) for every eligible pair and layer. -/
def SelSucc (ξ : SurvBits S.P.n S.P.J) (sc : SelCoins S.P.n S.P.J S.P.R S.b) : Prop :=
  ∀ e, Eligible S.F e → ∀ k ≤ S.P.J, |S.y ξ sc e k - S.xr e * S.surv ξ e k| ≤ S.t e k / 24

/-- The baseline layer `k_e = min {k ≥ 0 : x_e ≥ 5 t_e(k)/24}` (15). -/
def kBase (e : Pair S.P.n) : ℕ :=
  if h : ∃ k : ℕ, 5 * S.t e k / 24 ≤ S.xr e then Nat.find h else 0

/-- The hypothetical query `y⁺_e(k) = y_e(k) + x_e (1 − I_{e,k})`. -/
def yPlus (ξ : SurvBits S.P.n S.P.J) (sc : SelCoins S.P.n S.P.J S.P.R S.b) (e : Pair S.P.n)
    (k : ℕ) : ℝ :=
  S.y ξ sc e k + S.xr e * (1 - S.surv ξ e k)

/-- `η_e = 1[y⁺_e(k_e) < θ_e(k_e)]` (16). -/
def η (ξ : SurvBits S.P.n S.P.J) (sc : SelCoins S.P.n S.P.J S.P.R S.b) (e : Pair S.P.n) : ℕ :=
  if S.yPlus ξ sc e (S.kBase e) < S.θ e (S.kBase e) then 1 else 0

/-- `j_e = k_e + η_e` (16). -/
def jLay (ξ : SurvBits S.P.n S.P.J) (sc : SelCoins S.P.n S.P.J S.P.R S.b) (e : Pair S.P.n) : ℕ :=
  S.kBase e + S.η ξ sc e

/-- The collision vector `v^{k,r}_e` of §4.3. -/
def coll (ξ : SurvBits S.P.n S.P.J) (dc : DiagCoins S.P.n S.P.J S.P.R S.P.bB) (e : Pair S.P.n)
    (k : ℕ) (r : Fin S.P.R) : Pair S.P.n → ℝ :=
  fun f => if f = e then 0 else
    ((S.sgnE e * sgnS (S.Se e) f * S.x f * S.surv ξ f k *
      (if dc.hT (S.lay k) r f = dc.hT (S.lay k) r e then 1 else 0) : ℤ) : ℝ)

/-- `v_e = v^{j_e, r_e}_e` for a selected pair, with `r_e` the row chosen at layer `ĵ_e`. -/
def vSel (ξ : SurvBits S.P.n S.P.J) (sc : SelCoins S.P.n S.P.J S.P.R S.b)
    (dc : DiagCoins S.P.n S.P.J S.P.R S.P.bB) (e : Pair S.P.n) : Pair S.P.n → ℝ :=
  match S.jhat ξ sc e with
  | none => 0
  | some k => match S.row ξ dc e k with
    | none => 0
    | some r => S.coll ξ dc e (S.jLay ξ sc e) r

/-- The conclusion of Lemma 4.4: `‖v_e‖₂ ≤ t_e(j_e)/18` for every pair selected by pair
enumeration. -/
def DiagOK (ξ : SurvBits S.P.n S.P.J) (sc : SelCoins S.P.n S.P.J S.P.R S.b)
    (dc : DiagCoins S.P.n S.P.J S.P.R S.P.bB) : Prop :=
  ∀ e ∈ S.selected ξ sc S.enumCands, l2 (S.vSel ξ sc dc e) ≤ S.t e (S.jLay ξ sc e) / 18

end Setup

/-- An Appendix A.4 seed: four field elements of `F_{2^m}`. -/
abbrev A4Seed (m : ℕ) := Fin 4 → Fin (2 ^ m)

/-- The seeds of one copy (§7.3–7.4): A.4 seeds of the selection hashes and signs, of the
estimation hashes and of the diagnostic signs, and the seeds of the survival and evaluation tapes. -/
abbrev CopySeeds (P : SketchParams) (m s₁ s₂ : ℕ) :=
  ((Fin (P.J + 1) → Fin P.R → A4Seed m) × (Fin (P.J + 1) → Fin P.R → A4Seed m)) ×
    ((Fin (P.J + 1) → Fin P.R → A4Seed m) ×
      (Fin (P.J + 1) → Fin P.R → Fin (32 * P.R) → Fin 2 → A4Seed m)) ×
    (Fin s₁ → Bool) × (Fin s₂ → Bool)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- The finitely many seeds of one copy. -/
noncomputable instance (P : SketchParams) (m s₁ s₂ : ℕ) : Fintype (CopySeeds P m s₁ s₂) := by
  unfold CopySeeds A4Seed; infer_instance

/-- The tables of one copy whose four-wise families are those of Appendix A.4 over `F_{2^m}` and
whose survival bits and evaluation signs are the tapes `tξ`, `tσ` of their seeds. -/
def Sketch.copyTables (K : Sketch) {m s₁ s₂ : ℕ} (tξ : (Fin s₁ → Bool) → SurvBits K.P.n K.P.J)
    (tσ : (Fin s₂ → Bool) → EvalSigns K.P.n K.P.J K.P.R) (sd : CopySeeds K.P m s₁ s₂) :
    Tables K.P K.b :=
  K.tables (tξ sd.2.2.1) (SelCoins.ofSeeds (a4Hash m K.b) (a4Sign m) sd.1)
    (DiagCoins.ofSeeds (a4Hash m K.P.bB) (a4Sign m) sd.2.1) (tσ sd.2.2.2)

/-- The result of recovery with candidate discovery for one copy (Appendix A.4 families, tapes
`tξ`, `tσ`). -/
def Setup.copyResult (S : Setup) {m s₁ s₂ : ℕ} (tξ : (Fin s₁ → Bool) → SurvBits S.P.n S.P.J)
    (tσ : (Fin s₂ → Bool) → EvalSigns S.P.n S.P.J S.P.R) (sd : CopySeeds S.P m s₁ s₂) :
    Option (Pair S.P.n → ℝ) :=
  S.decode (tξ sd.2.2.1) (SelCoins.ofSeeds (a4Hash m S.b) (a4Sign m) sd.1)
    (DiagCoins.ofSeeds (a4Hash m S.P.bB) (a4Sign m) sd.2.1) (tσ sd.2.2.2)
    (S.discCands (tξ sd.2.2.1) (SelCoins.ofSeeds (a4Hash m S.b) (a4Sign m) sd.1))

/-- The output list `L` of an implementation agrees with the decoder's result: the empty list on
abort, and otherwise the graph `H`, each edge listed once with its weight. -/
def OutputMatches {n : ℕ} (res : Option (Pair n → ℝ)) (L : List (Pair n × ℚ)) : Prop :=
  match res with
  | none => L = []
  | some H => (L.map Prod.fst).Nodup ∧ (∀ p ∈ L, ((p.2 : ℚ) : ℝ) = H p.1 ∧ H p.1 ≠ 0) ∧
      ∀ e, H e ≠ 0 → ∃ p ∈ L, p.1 = e

end TurnstileCutSparsify.Main


