-- Prove2me | Definitions.Def_GaussLocalMaxColoring_Main_Bands
-- name    : GaussLocalMaxColoring_Main_Bands
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:22:07.852493+00:00
-- url     : https://prove2.me/theorems/c915e8d9-0a8e-457e-8fd7-4549ec79a466
-- title:
--   Band partitions, $\Theta_1,\Theta_2$ feasibility, $\Gamma_{rx}(X)$, the guarantee of BuildVector (Lemma 34), band rounding (Algorithms 4, 5), VectorColoring's grid, SparseProgress (Algorithm 3)
-- statement:
--   **Bands** (§5.2). A partition $\mathcal P$ of $[-\tfrac12,1]$ into nonempty, pairwise disjoint intervals (each endpoint included or not) of length $\le 1/\log n$, each inside $[-\tfrac12,0]$ or $[0,1]$. $S_{r,P}=\{x:\langle v_r,v_x\rangle\in P\}$; $P$ is positive iff $P\subseteq[0,1]$; $\rho_P=\inf P$ (positive) or $\sup P$ (negative).
--
--   **Auxiliary SDPs** (§5.1). A witness $(x_\emptyset,\{x_{i,c}\})$, given by its Gram matrix $Y$, is feasible for $\Theta_m(S)$ ($m\in\{1,2\}$) if $\|x_\emptyset\|^2=1$, $\langle x_\emptyset,x_{i,c}\rangle=\|x_{i,c}\|^2$, $\langle x_{i,c},x_{i,c'}\rangle=0$ ($c\ne c'$), $\langle x_{i,c},x_{j,c}\rangle=0$ and $\langle x_\emptyset-x_i,x_\emptyset-x_j\rangle\ge0$ for $ij\in E[S]$, with $x_i=\sum_{c\le m}x_{i,c}$.
--
--   **$\Gamma_{rx}(X)$** (p. 33), indexed by $N_V(r)\sqcup N_V(x)$: $(\Gamma_{rx}(X))_{(i,j),(i',j')}=\frac{1+\mathbf 1_{i\ne i'}}3(4X_{jj'}+2X_{ji'}+2X_{ij'}+X_{ii'})$.
--
--   **Lemma 34's guarantee** ($\varepsilon_{\rm SDP}=e^{-3n}$): $X_{ii}=1$, $-\tfrac12\le X_{ij}\le1$, $X_{ij}\le-\tfrac12+\varepsilon_{\rm SDP}$ on edges, $X_{ij}+X_{ij'}\le\tfrac12$ for $jj'\in E$, $i\notin\{j,j'\}$, $\Gamma_{rx}(X)\succeq-\varepsilon_{\rm SDP}I$ on edges; for every $r$ and $P\in\mathcal P$ with $S=S_{r,P}$: (i) $P$ positive: the witness is feasible for $\Theta_1(S)$ and $\sum_{j\in S}\|x_j\|^2\ge\sum_{j\in S}\frac{1+2X_{rj}}3-\varepsilon_{\rm SDP}\ge\frac{1+2\rho_P}3|S|-\varepsilon_{\rm SDP}$; (ii) $P$ negative: feasible for $\Theta_2(S)$ and $\sum_{j\in S}(\|x_{j,1}\|^2+\|x_{j,2}\|^2)\ge\sum_{j\in S}\frac{2-2X_{rj}}3-\varepsilon_{\rm SDP}\ge\frac{2-2\rho_P}3|S|-\varepsilon_{\rm SDP}$. `BVGuarantee` states this for real vectors $v$ and witness vectors $W$ ($X$, $Y$ their Gram matrices). `ExactSDPVectors` is the §5 analysis convention: unit vectors, $-\tfrac12\le\langle v_i,v_j\rangle\le1$, $\langle v_i,v_j\rangle=-\tfrac12$ on edges, and the third constraint.
--
--   **Band rounding.** RoundPositive: $\tau=\frac{1+2\rho_P}3-\varepsilon_{\rm thr}$, $S'=\{i\in S:\|x_i\|^2\ge\tau\}$, $I_0$ the isolated vertices of $G[S']$, $S''=S'\setminus I_0$, VectorColoring on $G[S'']$ with $k=1/\tau$, $I=I_0\cup I'$. RoundNegative: $\tau=\frac{2-2\rho_P}3-\varepsilon_{\rm thr}$, $S'=\{i:\|x_{i,1}\|^2+\|x_{i,2}\|^2\ge\tau\}$, VectorColoring on $G[S']$ with $k=\frac{3\tau-1}{2\tau-1}$, $I=I'$. Each returns SUCCESS iff $|I|\ge T$.
--
--   **VectorColoring** runs Theorem 2's algorithm with $k_h=\min\{k'\in\{2+h,\dots,4\}:k'\ge k\}$ and $\beta_h(G')=\min\{\beta'\in\{h,\dots,1\}:\Delta(G')\le|V(G')|^{\beta'}\}$. It **meets its guarantee** with a returned set $I'$ (relative to an $o(1)$ family $g$, one function per grid pair) if $I'\subseteq V(G')$ is independent and, for $V(G')\ne\emptyset$, $|I'|\ge|V(G')|^{1-\frac{(k_h-2)\beta_h}{2+k_h\beta_h}-g_{k_h,\beta_h}(|V(G')|)}$.
--
--   **SparseProgress** (Algorithm 3), one trial after BuildVector: process the bands in a given order, return the first band's set of size $\ge T$, else run Algorithm 2 with Table 3 parameters.
--
--   **Formalization Note.** Witness vectors enter only through their Gram matrices; for $\Theta_1$ only colour $c=0$ is used ($x_j=x_{j,0}$). VectorColoring's returned set is an argument of the band rounding (its randomness is modelled where used). $k_h$ is computed by the formula $2+h\max\{1,\lceil (k-2)/h\rceil\}$, the minimum of the grid above $k$ for $k\le4$ (the paper shows $k\in(2,4]$).
-- source:
--   Deguchi, Kawarabayashi, Yoneda, Yoneda (2026), An O(n^0.1537)-Coloring Algorithm for 3-Colorable Graphs, arXiv:2610.35859 (SHA-256 9917b0a1…), §5.1–§5.2 (printed pp. 31–35, PDF 33–37), Lemma 34 (p. 33), Algorithms 3–5 (pp. 34–35)

import Mathlib
import Definitions.Def_GaussLocalMaxColoring_Main_Iterative
import Definitions.Def_GaussLocalMaxColoring_Main_Section5

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main
open Classical
noncomputable section

namespace GaussLocalMaxColoring.Main

/-! # Bands, the auxiliary SDPs `Θ₁, Θ₂`, `Γ_rx(X)`, the guarantee of BuildVector (Lemma 34),
band rounding (Algorithms 4, 5), VectorColoring's grid, and SparseProgress (Algorithm 3)

Deguchi–Kawarabayashi–Yoneda–Yoneda, arXiv:2610.35859, §5.1–§5.2 (pp. 31–35, PDF 33–37).

**Formalization Note.**
* An interval of the partition `𝒫` is given by its endpoints and whether each endpoint belongs
  to it; a band partition is a finite set `Pt` (the paper's `𝒫`) of nonempty, pairwise disjoint intervals with union
  `[−1/2, 1]`, each of length at most `1/log n` and contained in `[−1/2, 0]` or in `[0, 1]`.
  The count bound `|Pt| = O(log n)` is stated where it is used.
* Every quantity of Lemma 34 depends on the vectors only through their Gram matrices: the
  vectors `{v_i}` through `X_ij = ⟨v_i, v_j⟩`, and the witness `𝒲_{r,P}` (vectors `x_∅` and
  `x_{j,c}`, `j ∈ S`, `c ∈ {1, 2}`, written `c = 0, 1` here) through its Gram matrix `Y`, indexed by
  `Option (Fin n × Fin 2)` (`none` is `x_∅`). For `Θ₁` only the colour `c = 0` is used and
  `x_j = x_{j,0}`; for `Θ₂`, `x_j = x_{j,0} + x_{j,1}`.
* VectorColoring (the algorithm of Theorem 2 run with `k_h` and `β_h(G′)`) is not fixed here: a
  band rounding takes VectorColoring's returned set `I′` as an argument, and "the internal call
  meets its guarantee" is the predicate `VCMeets` on `I′`, relative to a family `g` of `o(1)`
  functions, one for each grid pair `(k_h, β_h)`. -/

variable {n d : ℕ}

/-- An interval of reals with endpoints `lo ≤ hi`, each endpoint included or not. -/
structure Ival where
  lo : ℝ
  hi : ℝ
  loIn : Bool
  hiIn : Bool

/-- The set of reals of an interval. -/
def Ival.toSet (P : Ival) : Set ℝ :=
  {x | (if P.loIn then P.lo ≤ x else P.lo < x) ∧ (if P.hiIn then x ≤ P.hi else x < P.hi)}

/-- `Pt` is a partition of `[−1/2, 1]` into nonempty intervals of length at most `1/log n`, each
contained in `[−1/2, 0]` or in `[0, 1]` (§5.2, "Bands"). -/
def IsBandPartition (n : ℕ) (Pt : Finset Ival) : Prop :=
  (∀ P ∈ Pt, P.toSet.Nonempty) ∧
  (∀ P ∈ Pt, ∀ Q ∈ Pt, P ≠ Q → Disjoint P.toSet Q.toSet) ∧
  (⋃ P ∈ Pt, P.toSet) = Set.Icc (-(1 / 2 : ℝ)) 1 ∧
  (∀ P ∈ Pt, P.hi - P.lo ≤ 1 / Real.log n) ∧
  (∀ P ∈ Pt, P.toSet ⊆ Set.Icc (-(1 / 2 : ℝ)) 0 ∨ P.toSet ⊆ Set.Icc 0 1)

/-- `P` (and its bands) is positive iff `P ⊆ [0, 1]`. -/
def Ival.Positive (P : Ival) : Prop := P.toSet ⊆ Set.Icc 0 1

/-- `ρ_P = inf P` for a positive interval and `sup P` for a negative one. -/
def Ival.rhoP (P : Ival) : ℝ := if P.Positive then sInf P.toSet else sSup P.toSet

/-- The Gram matrix of a family of vectors. -/
def gram {ι : Type*} (x : ι → Space d) : Matrix ι ι ℝ := Matrix.of fun i j => ⟪x i, x j⟫

/-- The band `S_{r,P} = {x ∈ V : X_rx ∈ P}` of a Gram matrix `X` (for `X = gram v`,
`{x : ⟨v_r, v_x⟩ ∈ P}`). -/
def band (X : Matrix (Fin n) (Fin n) ℝ) (r : Fin n) (P : Ival) : Finset (Fin n) :=
  Finset.univ.filter fun x => X r x ∈ P.toSet

/-- Index of the witness vectors: `none` is `x_∅`, `some (j, c)` is `x_{j,c}`. -/
abbrev WIdx (n : ℕ) := Option (Fin n × Fin 2)

/-- Feasibility of a witness (given by its Gram matrix `Y`) for `Θ_m(S)`, `m ∈ {1, 2}` (§5.1):
`‖x_∅‖² = 1`, `⟨x_∅, x_{i,c}⟩ = ‖x_{i,c}‖²`, `⟨x_{i,c}, x_{i,c′}⟩ = 0` (`c ≠ c′`),
`⟨x_{i,c}, x_{j,c}⟩ = 0` and `⟨x_∅ − x_i, x_∅ − x_j⟩ ≥ 0` for `ij ∈ E[S]`, `x_i = Σ_{c<m} x_{i,c}`. -/
def ThetaFeasible (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (m : ℕ)
    (Y : Matrix (WIdx n) (WIdx n) ℝ) : Prop :=
  Y none none = 1 ∧
  (∀ i ∈ S, ∀ c : Fin 2, c.val < m → Y none (some (i, c)) = Y (some (i, c)) (some (i, c))) ∧
  (∀ i ∈ S, ∀ c c' : Fin 2, c.val < m → c'.val < m → c ≠ c' →
    Y (some (i, c)) (some (i, c')) = 0) ∧
  (∀ i ∈ S, ∀ j ∈ S, G.Adj i j → ∀ c : Fin 2, c.val < m → Y (some (i, c)) (some (j, c)) = 0) ∧
  (∀ i ∈ S, ∀ j ∈ S, G.Adj i j →
    0 ≤ 1 - (∑ c : Fin 2 with c.val < m, Y none (some (j, c)))
      - (∑ c : Fin 2 with c.val < m, Y (some (i, c)) none)
      + ∑ c : Fin 2 with c.val < m, ∑ c' : Fin 2 with c'.val < m, Y (some (i, c)) (some (j, c')))

/-- `Γ_rx(X)` (p. 33): indexed by the disjoint union `N_V(r) ⊔ N_V(x)` (pairs `(b, j)` with
`b = 0` for `r`, `b = 1` for `x`, and `j` a neighbour of that vertex),
`(Γ_rx(X))_{(i,j),(i′,j′)} = ((1 + 1_{i≠i′})/3)(4X_{jj′} + 2X_{ji′} + 2X_{ij′} + X_{ii′})`. -/
def Gamma (G : SimpleGraph (Fin n)) (X : Matrix (Fin n) (Fin n) ℝ) (r x : Fin n) :
    Matrix {p : Fin 2 × Fin n // G.Adj (if p.1 = 0 then r else x) p.2}
      {p : Fin 2 × Fin n // G.Adj (if p.1 = 0 then r else x) p.2} ℝ :=
  Matrix.of fun p q =>
    let i := if p.1.1 = 0 then r else x
    let i' := if q.1.1 = 0 then r else x
    (1 + if p.1.1 = q.1.1 then 0 else 1) / 3 *
      (4 * X p.1.2 q.1.2 + 2 * X p.1.2 i' + 2 * X i q.1.2 + X i i')

/-- `ε_SDP = e^{−3n}` (§3.1, p. 12). -/
def epsSDP (n : ℕ) : ℝ := Real.exp (-(3 * n : ℝ))

/-- The vector guarantees of **Lemma 34** on the Gram matrix `X` of `{v_i}`: unit diagonal,
`−1/2 ≤ X_ij ≤ 1`, `X_ij ≤ −1/2 + ε` on edges, `X_ij + X_ij′ ≤ 1/2` for `jj′ ∈ E`,
`i ∉ {j, j′}`, and `Γ_rx(X) ⪰ −ε I` for `rx ∈ E`. -/
def BVVectorConds (G : SimpleGraph (Fin n)) (X : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) : Prop :=
  (∀ i, X i i = 1) ∧ (∀ i j, -(1 / 2) ≤ X i j ∧ X i j ≤ 1) ∧
  (∀ i j, G.Adj i j → X i j ≤ -(1 / 2) + ε) ∧
  (∀ j j', G.Adj j j' → ∀ i, i ≠ j → i ≠ j' → X i j + X i j' ≤ 1 / 2) ∧
  (∀ r x, G.Adj r x → (Gamma G X r x + ε • (1 : Matrix _ _ ℝ)).PosSemidef)

/-- The band-witness guarantees (i), (ii) of **Lemma 34** for every `r ∈ V`, `P ∈ Pt`. -/
def BVWitnessConds (G : SimpleGraph (Fin n)) (X : Matrix (Fin n) (Fin n) ℝ) (Pt : Finset Ival)
    (Y : Fin n → Ival → Matrix (WIdx n) (WIdx n) ℝ) (ε : ℝ) : Prop :=
  ∀ r, ∀ P ∈ Pt,
    (P.Positive →
      ThetaFeasible G (band X r P) 1 (Y r P) ∧
      (∑ j ∈ band X r P, Y r P (some (j, 0)) (some (j, 0))) ≥
        (∑ j ∈ band X r P, (1 + 2 * X r j) / 3) - ε ∧
      (∑ j ∈ band X r P, (1 + 2 * X r j) / 3) - ε ≥
        (1 + 2 * P.rhoP) / 3 * (band X r P).card - ε) ∧
    (¬ P.Positive →
      ThetaFeasible G (band X r P) 2 (Y r P) ∧
      (∑ j ∈ band X r P, (Y r P (some (j, 0)) (some (j, 0)) + Y r P (some (j, 1)) (some (j, 1)))) ≥
        (∑ j ∈ band X r P, (2 - 2 * X r j) / 3) - ε ∧
      (∑ j ∈ band X r P, (2 - 2 * X r j) / 3) - ε ≥
        (2 - 2 * P.rhoP) / 3 * (band X r P).card - ε)

/-- An output `({v_i}, 𝒮)` of BuildVector with the guarantees of **Lemma 34**, `ε = ε_SDP`:
vectors `v` and witness vectors `W r P` (in a common dimension `d'`). -/
def BVGuarantee {d' : ℕ} (G : SimpleGraph (Fin n)) (Pt : Finset Ival) (v : Fin n → Space d)
    (W : Fin n → Ival → WIdx n → Space d') : Prop :=
  BVVectorConds G (gram v) (epsSDP n) ∧
  BVWitnessConds G (gram v) Pt (fun r P => gram (W r P)) (epsSDP n)

/-- The §5 analysis convention (p. 35): unit vectors with `−1/2 ≤ ⟨v_i, v_j⟩ ≤ 1`, the edge
constraint exact (`⟨v_i, v_j⟩ = −1/2` on edges) and `⟨v_i, v_j⟩ + ⟨v_i, v_j′⟩ ≤ 1/2` for
`jj′ ∈ E`, `i ∉ {j, j′}`. (`Γ_rx(X) ⪰ 0` is stated separately where used.) -/
def ExactSDPVectors (G : SimpleGraph (Fin n)) (v : Fin n → Space d) : Prop :=
  (∀ i, ‖v i‖ = 1) ∧ (∀ i j, -(1 / 2) ≤ ⟪v i, v j⟫ ∧ ⟪v i, v j⟫ ≤ 1) ∧
  (∀ i j, G.Adj i j → ⟪v i, v j⟫ = -(1 / 2)) ∧
  (∀ j j', G.Adj j j' → ∀ i, i ≠ j → i ≠ j' → ⟪v i, v j⟫ + ⟪v i, v j'⟫ ≤ 1 / 2)

/-! ### Band rounding (Algorithms 4 and 5) -/

/-- RoundPositive's threshold `τ = (1 + 2ρ_P)/3 − ε_thr`. -/
def tauPos (P : Ival) (εthr : ℝ) : ℝ := (1 + 2 * P.rhoP) / 3 - εthr

/-- RoundNegative's threshold `τ = (2 − 2ρ_P)/3 − ε_thr`. -/
def tauNeg (P : Ival) (εthr : ℝ) : ℝ := (2 - 2 * P.rhoP) / 3 - εthr

/-- RoundPositive's `S′ = {i ∈ S : ‖x_i‖² ≥ τ}`. -/
def sPrimePos (S : Finset (Fin n)) (Y : Matrix (WIdx n) (WIdx n) ℝ) (τ : ℝ) : Finset (Fin n) :=
  S.filter fun i => τ ≤ Y (some (i, 0)) (some (i, 0))

/-- RoundNegative's `S′ = {i ∈ S : ‖x_{i,1}‖² + ‖x_{i,2}‖² ≥ τ}`. -/
def sPrimeNeg (S : Finset (Fin n)) (Y : Matrix (WIdx n) (WIdx n) ℝ) (τ : ℝ) : Finset (Fin n) :=
  S.filter fun i => τ ≤ Y (some (i, 0)) (some (i, 0)) + Y (some (i, 1)) (some (i, 1))

/-- `I₀ = {i ∈ S′ : N_{S′}(i) = ∅}`, the isolated vertices of `G[S′]`. -/
def isolatedIn (G : SimpleGraph (Fin n)) (S' : Finset (Fin n)) : Finset (Fin n) :=
  S'.filter fun i => nbr G S' i = ∅

/-- The vertex set of VectorColoring's input graph in a band rounding: `S″ = S′ ∖ I₀` (positive),
`S′` (negative). -/
def vcInput (G : SimpleGraph (Fin n)) (X : Matrix (Fin n) (Fin n) ℝ) (r : Fin n) (P : Ival)
    (Y : Matrix (WIdx n) (WIdx n) ℝ) (εthr : ℝ) : Finset (Fin n) :=
  if P.Positive then
    sPrimePos (band X r P) Y (tauPos P εthr) \
      isolatedIn G (sPrimePos (band X r P) Y (tauPos P εthr))
  else sPrimeNeg (band X r P) Y (tauNeg P εthr)

/-- VectorColoring's `k` in a band rounding: `1/τ` (positive), `(3τ−1)/(2τ−1)` (negative). -/
def vcK (P : Ival) (εthr : ℝ) : ℝ :=
  if P.Positive then 1 / tauPos P εthr
  else (3 * tauNeg P εthr - 1) / (2 * tauNeg P εthr - 1)

/-- The set constructed by the band rounding of band `S_{r,P}` from VectorColoring's returned set
`I′`: `I₀ ∪ I′` (RoundPositive, line 7) or `I′` (RoundNegative, line 4). It returns `SUCCESS`
iff this set has size `≥ T`. -/
def bandOut (G : SimpleGraph (Fin n)) (X : Matrix (Fin n) (Fin n) ℝ) (r : Fin n) (P : Ival)
    (Y : Matrix (WIdx n) (WIdx n) ℝ) (εthr : ℝ) (I' : Finset (Fin n)) : Finset (Fin n) :=
  if P.Positive then isolatedIn G (sPrimePos (band X r P) Y (tauPos P εthr)) ∪ I' else I'

/-- `k_h = min{k′ ∈ 𝒦_h : k′ ≥ k}`, `𝒦_h = {2+h, 2+2h, …, 4}` (for `k ≤ 4`). -/
def kGrid (h k : ℝ) : ℝ := 2 + h * (max 1 ⌈(k - 2) / h⌉ : ℤ)

/-- `β_h(G[S]) = min{β′ ∈ 𝒟_h : Δ(G[S]) ≤ |S|^{β′}}`, `𝒟_h = {h, 2h, …, 1}` (`1/h ∈ ℕ`). -/
def betaGrid (h : ℝ) (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : ℝ :=
  h * (sInf {i : ℕ | 1 ≤ i ∧ (maxDegOn G S : ℝ) ≤ (S.card : ℝ) ^ (h * i)} : ℕ)

/-- The exponent `1 − (k−2)β′/(2 + kβ′)` of VectorColoring's guarantee (p. 37). -/
def vcExp (k β' : ℝ) : ℝ := 1 - (k - 2) * β' / (2 + k * β')

/-- VectorColoring, called on `G[S]` with parameter `k`, **meets its guarantee** with `I′`
(relative to the `o(1)` family `g`): `I′ ⊆ S` is independent and, for nonempty `S`,
`|I′| ≥ |S|^{1 − (k_h−2)β_h/(2+k_hβ_h) − g_{k_h,β_h}(|S|)}`. -/
def VCMeets (g : ℝ → ℝ → ℕ → ℝ) (h k : ℝ) (G : SimpleGraph (Fin n)) (S I' : Finset (Fin n)) :
    Prop :=
  I' ⊆ S ∧ IsIndep G I' ∧
  (S.Nonempty →
    (S.card : ℝ) ^ (vcExp (kGrid h k) (betaGrid h G S) -
      g (kGrid h k) (betaGrid h G S) S.card) ≤ I'.card)

/-! ### SparseProgress (Algorithm 3) -/

/-- One trial of **SparseProgress** after BuildVector, with Table 3 parameters: the bands are
processed in the order of the list `L`; band `(r, P)` rounds with VectorColoring's returned set
`vc r P`; the first band whose constructed set has size `≥ T` is returned; otherwise the result
of Algorithm 2 (samples `ω`) is returned. `none` is `FAIL`. -/
def sparseTrial (G : SimpleGraph (Fin n)) (v : Fin n → Space d) {d' : ℕ}
    (W : Fin n → Ival → WIdx n → Space d') (εthr : ℝ) (L : List (Fin n × Ival))
    (vc : Fin n → Ival → Finset (Fin n))
    (ω : Fin (numLevels n) × Fin (runs5 n) → Space d) : Option (Finset (Fin n)) :=
  match L.find? (fun b => target5 n ≤
      (bandOut G (gram v) b.1 b.2 (gram (W b.1 b.2)) εthr (vc b.1 b.2)).card) with
  | some b => some (bandOut G (gram v) b.1 b.2 (gram (W b.1 b.2)) εthr (vc b.1 b.2))
  | none => alg2 G v (delta5 n) (target5 n) ω

/-- A trial's result is an independent set of size at least `T`. -/
def TrialGood (G : SimpleGraph (Fin n)) (o : Option (Finset (Fin n))) : Prop :=
  ∃ I, o = some I ∧ IsIndep G I ∧ target5 n ≤ I.card

end GaussLocalMaxColoring.Main


