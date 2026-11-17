-- Prove2me | Definitions.Def_NoisyOWMPC_Supplement_selectorF12
-- name    : NoisyOWMPC_Supplement_selectorF12
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:04:16.377203+00:00
-- url     : https://prove2.me/theorems/508b58af-e297-40a5-8ba1-bfd9101eb405
-- title:
--   Construction F.12: the verifiable selector from periodic signed counts
-- statement:
--   Let $m$ be the number of sign rows, $n = 2m^{16} + 1$ and $N = mn$; partition $[N]$ into $m$ segments of size $n$ and write $u_j \in \{0,1\}^n$ for the characteristic vector of $U \subseteq [N]$ on segment $j$. With $a_n = \lceil n^{11/20}\rceil$, $b_n = \lceil n^{2/5}\rceil$ and $P_n = 4\lceil n^{9/20}/4\rceil$, a **sign row** is $e \in E_n = \{e \in \{-1,1\}^n : \sum_s e_s = -1\}$, and for $u \in \{0,1\}^n$
--   $$
--   W(u) = \sum_s u_s,\quad g(u) = \mathbf 1\big[|W(u) - n/2| \le a_n\big],\quad S_e(u) = \sum_s e_s u_s,\quad B_e(u) = \mathrm{Mod}_{P_n}(S_e(u)).
--   $$
--   The row $e$ is **robust** at $v$ if $|S_e(v) - z| \ge b_n$ for every integer $z$ with $\mathrm{Mod}_{P_n}(z) \ne \mathrm{Mod}_{P_n}(S_e(v))$.
--
--   **Construction F.12.**
--
--   1. $\mathrm{Gen_{sel}}$: independent uniform sign rows $e_1, \dots, e_m \in E_n$, $K = (e_j)_j$.
--   2. $\mathrm{Guard_{sel}}(U) = \prod_j g(u_j)$ and $b_K(U) = \mathbf 1\big[\sum_j B_{e_j}(u_j) > m/2\big]$.
--   3. $\mathrm{Valid_{sel}}(K) = 1$ iff $K$ consists of $m$ rows in $E_n$.
--   4. $\mathrm{SampleSt_{sel}}$: a table of independent uniform $e_{j,\zeta} \in E_n$, $j \in [m]$, $\zeta \in H_{\mathrm{sel}}$; $\mathrm{Recons_{sel}}(T, \xi) = (e_{j, \gamma^{\mathrm{sel}}_j(\xi)})_j$.
--   5. $\mathrm{Rec_{sel}}(T, V, U)$: the empty list if $U \not\subseteq V$ or either set fails the guard; otherwise the candidate lists $L^{\mathrm{raw}}_j = \{\zeta : e_{j,\zeta} \text{ robust at } v_j,\ B_{e_{j,\zeta}}(u_j) \ne B_{e_{j,\zeta}}(v_j)\}$, each discarded if larger than $m^{16}$, are decoded by the expander $G_{\mathrm{sel}}$ ($m$ layers, $\ell = m^{16}$, $G = \lceil m^{2/5}\rceil$).
--
--   It instantiates the verifiable selector of Construction E.8 in Theorem E.10.
--
--   **Formalization Note** Keys range over all $m$-tuples of $\pm 1$ rows of length $n$, so that $\mathrm{Valid_{sel}}$ is meaningful; $\mathrm{Gen_{sel}}$ is uniform on the valid ones. The expander is taken from a family satisfying Corollary A.8.
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Lemma F.11 (parameters), p.72; Parameters and row predicate, (F.7), pp.72–73; Construction F.12, p.73

import Mathlib
import Definitions.Def_NoisyOWMPC_Supplement_Verifiable
import Definitions.Def_NoisyOWMPC_Supplement_periodic
import Definitions.Def_NoisyOWMPC_releaseTest
import Definitions.Def_NoisyOWMPC_LayeredGraph

namespace NoisyOWMPC.Supplement

/-- The segment length `n = 2m¹⁶ + 1` (Ishai, Lu, Zafar, STOC 2027 submission (manuscript sha256
3a9569fa…), Lemma F.11, p.72). -/
def nSeg (m : ℕ → ℕ) (lam : ℕ) : ℕ := 2 * m lam ^ 16 + 1

/-- The block length `N = mn` (Lemma F.11, p.72). -/
def NF12 (m : ℕ → ℕ) (lam : ℕ) : ℕ := m lam * nSeg m lam

/-- The signed sum `∑_s e_s` of a sign row `e ∈ {−1, 1}ⁿ`, the sign `+1` being `true`. -/
def signSum {n : ℕ} (e : Fin n → Bool) : ℤ := ∑ s, if e s then 1 else -1

/-- A **sign row** `e ∈ E_n = {e ∈ {−1,1}ⁿ : ∑_s e_s = −1}` (p.73: "with one more negative than
positive sign"). -/
def IsSignRow {n : ℕ} (e : Fin n → Bool) : Prop := signSum e = -1

/-- The characteristic vector `u_j ∈ {0,1}ⁿ` of the restriction of `U ⊆ [N]` to segment `j`, the
segments being the blocks `jn, …, (j + 1)n − 1` of `[N]` (p.72: "Partition `[N]` into `m` disjoint
segments `N₁, …, N_m` of size `n`, and identify the restriction of a set `U ⊆ [N]` to segment `j`
with its characteristic vector `u_j ∈ {0,1}ⁿ`"). -/
def segVec {m n : ℕ} (U : Finset (Fin (m * n))) (j : Fin m) : Fin n → Bool :=
  fun s => decide (finProdFinEquiv (j, s) ∈ U)

/-- The count `W(u) = ∑_s u_s` (F.7). -/
def cntW {n : ℕ} (u : Fin n → Bool) : ℕ := (Finset.univ.filter fun s => u s = true).card

/-- The segment guard `g(u) = 1[|W(u) − n/2| ≤ a_n]` with `a_n = ⌈n^{11/20}⌉` (F.7). -/
noncomputable def segGuard {n : ℕ} (u : Fin n → Bool) : Bool :=
  decide (|(cntW u : ℝ) - (n : ℝ) / 2| ≤ (aTol n : ℝ))

/-- The signed count `S_e(u) = ∑_s e_s u_s` (F.7). -/
def sCount {n : ℕ} (e u : Fin n → Bool) : ℤ :=
  ∑ s, (if e s then (1 : ℤ) else -1) * (if u s then 1 else 0)

/-- The row bit `B_e(u) = Mod_{P_n}(S_e(u))` (F.7). -/
noncomputable def rowBit {n : ℕ} (e u : Fin n → Bool) : Bool := modP (pPer n) (sCount e u)

/-- The row `e` is **robust at `v`**, `Rob_e(v) = 1[d_{P_n}(S_e(v)) ≥ b_n]`, with
`d_P(s) = min{|s − z| : z ∈ ℤ, Mod_P(z) ≠ Mod_P(s)}` and `b_n = ⌈n^{2/5}⌉` (p.73). -/
def Robust {n : ℕ} (e v : Fin n → Bool) : Prop :=
  FarFrom (pPer n) (!modP (pPer n) (sCount e v)) (bMar n) (sCount e v)

open Classical in
/-- `Guard_sel(U) = ∏_{j=1}^m g(u_j)` (Construction F.12, p.73). -/
noncomputable def guardF12 {m n : ℕ} (U : Finset (Fin (m * n))) : Bool :=
  decide (∀ j, segGuard (segVec U j) = true)

open Classical in
/-- `b_K(U) = 1[∑_{j=1}^m B_{e_j}(u_j) > m/2]` (Construction F.12, p.73). -/
noncomputable def coinF12 {m n : ℕ} (K : Fin m → Fin n → Bool) (U : Finset (Fin (m * n))) : Bool :=
  decide (m < 2 * (Finset.univ.filter fun j => rowBit (K j) (segVec U j) = true).card)

/-- The selector expander `G_sel`: the layered `(m ℓ_sel, G, L_out)`-list-recoverable graph of the
family `Gr` with `m` layers, `ℓ_sel = m¹⁶` and `G = ⌈m^{2/5}⌉` (p.73). -/
noncomputable def gF12 (Gr : (M ℓ G : ℕ) → LayeredGraph M) (m : ℕ → ℕ) (lam : ℕ) :
    LayeredGraph (m lam) :=
  Gr (m lam) (m lam ^ 16) (gPar (m lam))

open Classical in
/-- The **recovery algorithm** `Rec_sel(T, V, U)` of Construction F.12 (p.73): the empty list if
`U ⊄ V` or either set fails the guard; otherwise, with
`L^raw_j(V, U) = {ζ ∈ H_sel : Rob_{e_{j,ζ}}(v_j) = 1 and B_{e_{j,ζ}}(u_j) ≠ B_{e_{j,ζ}}(v_j)}` and
`L_j(V, U) = L^raw_j(V, U)` if `|L^raw_j(V, U)| ≤ ℓ_sel = m¹⁶`, `∅` otherwise, return
`Rec_{G_sel}(⋃_j {j} × L_j(V, U))`. -/
noncomputable def recF12 {m n : ℕ} (G : LayeredGraph m)
    (T : Fin m → Fin G.h → {e : Fin n → Bool // IsSignRow e}) (V U : Finset (Fin (m * n))) :
    List (Fin G.κ → Bool) :=
  if ¬ U ⊆ V ∨ guardF12 U = false ∨ guardF12 V = false then [] else
  let raw : Fin m → Finset (Fin G.h) := fun j => Finset.univ.filter fun ζ =>
    Robust (T j ζ).1 (segVec V j) ∧ rowBit (T j ζ).1 (segVec U j) ≠ rowBit (T j ζ).1 (segVec V j)
  let L : Fin m → Finset (Fin G.h) := fun j => if (raw j).card ≤ m ^ 16 then raw j else ∅
  G.recov (Finset.univ.filter fun p : Fin m × Fin G.h => p.2 ∈ L p.1)

open Classical in
/-- **Construction F.12 (Verifiable selector)** (STOC 2027 submission (manuscript sha256
3a9569fa…), pp.72–73), with `m` sign rows, segment length `n = 2m¹⁶ + 1`, block length `N = mn`, and
the selector expander `G_sel` of the family `Gr`:
* `Gen_sel(1^λ)`: a uniform sign row `e_j ∈ E_n` for each `j ∈ [m]`, `K = (e_j)_j`;
* `Guard_sel(U) = ∏_j g(u_j)`; `b_K(U) = 1[∑_j B_{e_j}(u_j) > m/2]`;
* `Valid_sel(K) = 1` iff `K` consists of `m` rows in `E_n`;
* `SampleSt_sel(1^λ)`: independent uniform `e_{j,ζ} ∈ E_n` for `j ∈ [m]`, `ζ ∈ H_sel`, the table
  `T = (e_{j,ζ})_{j,ζ}`; `Recons_sel(T, ξ) = (e_{j,γ^sel_j(ξ)})_j`; `Rec_sel`: `recF12`.

**Formalization Note** Keys range over all `m`-tuples of `±1` rows of length `n` (so that
`Valid_sel` is meaningful); `Gen_sel` is uniform on the valid ones. Keys and tables are encoded by
their sign bits (`true` is `+1`). -/
noncomputable def selectorF12 (m : ℕ → ℕ) (Gr : (M ℓ G : ℕ) → LayeredGraph M) :
    VerSelector (NF12 m) where
  Key lam := Fin (m lam) → Fin (nSeg m lam) → Bool
  finKey lam := inferInstance
  genW lam K := if ∀ j, IsSignRow (K j) then
    1 / ((Finset.univ.filter fun K' : Fin (m lam) → Fin (nSeg m lam) → Bool =>
      ∀ j, IsSignRow (K' j)).card : ℝ) else 0
  enc lam K := (List.ofFn fun j => List.ofFn fun s => K j s).flatten
  guard lam U := guardF12 U
  coin lam K U := coinF12 K U
  κ lam := (gF12 Gr m lam).κ
  St lam := Fin (m lam) → Fin (gF12 Gr m lam).h → {e : Fin (nSeg m lam) → Bool // IsSignRow e}
  finSt lam := inferInstance
  sampW lam := unifW _
  encSt lam T := (List.ofFn fun j => (List.ofFn fun ζ => List.ofFn fun s => (T j ζ).1 s).flatten).flatten
  recons lam T ξ := fun j => (T j ((gF12 Gr m lam).γ j ξ)).1
  recov lam T V U := recF12 (gF12 Gr m lam) T V U
  valid lam K := decide (∀ j, IsSignRow (K j))

end NoisyOWMPC.Supplement


