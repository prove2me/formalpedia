-- Prove2me | Definitions.Def_PrivPACLower_ICP_Supplement_Classes
-- name    : PrivPACLower_ICP_Supplement_Classes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:09:46.447924+00:00
-- url     : https://prove2.me/theorems/a24af718-eb67-463c-9d22-ca2d3dc308fa
-- title:
--   Supplement hypothesis classes: boxes, interval unions, halfspaces, polygons, lines, subspaces, paths, product and union classes
-- statement:
--   The concrete classes of Sections 3, 5 and 6. Grid points are integers in $[N]=\{1,\dots,N\}$.
--
--   1. $B_{N,d}$: indicators of boxes $\prod_{j=1}^d[a_j,b_j]$ on $[N]^d$ with $1\le a_j\le b_j\le N$.
--   2. $I_{N,k}$: unions of at most $k$ integer intervals on $[N]$, including the empty union.
--   3. $H_{N,d}$: affine halfspaces $x\mapsto\mathbf 1\{\langle w,x\rangle\le\theta\}$ on $[N]^d$, $w\in\mathbb R^d$, $\theta\in\mathbb R$.
--   4. $C_{N,k}$: indicators of intersections of at most $k$ closed real halfplanes, restricted to $[N]^2$ (unbounded intersections allowed).
--   5. $\mathrm{Line}_p$: the $p^2$ functions $f_{a,b}(x,y)=\mathbf 1\{y=ax+b\}$ on $\mathbb Z_p^2$.
--   6. $S_{d,D}$: membership indicators of linear subspaces $V\subseteq\mathbb F_p^D$ with $\dim V\le d$.
--   7. $X_k$: binary strings of length at most $k$; $\mathrm{Path}_k=\{h_s:h_s(u)=\mathbf 1\{u\preceq s\},\ s\in\{0,1\}^k\}$ on $X_k$; $T_{d,k}$: on $X_{2k}$, $h_A(u)=\mathbf 1\{u\preceq s\text{ for some }s\in A\}$ for $A\subseteq\{0,1\}^{2k}$, $|A|\le d$.
--   8. For $1\le v\le D$ and block lengths $r_i\in\{\lfloor D/v\rfloor,\lceil D/v\rceil\}$ with $\sum_i r_i=D$, $N_i=2^{r_i}$: the **product class** $P_{v,D}$ on $\bigsqcup_i\{i\}\times[N_i]$ chooses one threshold $t_i\in\{0,\dots,N_i\}$ on each block independently; the **union class** $U_{v,D}=F_v\cup\mathrm{Thr}_{2^D-1}$ on $A\sqcup B$, $|A|=v$, $B=[2^D-1]$, contains every labelling of $A$ extended by zero on $B$ and every threshold on $B$ extended by zero on $A$.
--   9. $L_P=\log^*(\max\{2,D/v\})$ and $L_U=\log^*(\max\{2,D\})$.
--
--   These are the classes whose private sample complexities the supplement bounds.
--
--   **Formalization Note** "At most $k$ intervals" is encoded by exactly $k$ intervals $[a_i,b_i]$, an interval with $a_i>b_i$ being empty; "at most $k$ halfplanes" by $k$ rows $a_iz_1+b_iz_2\le c_i$, a row with $a_i=b_i=0$ being the whole plane or empty, which gives the same class on the grid. Dimension in $S_{d,D}$ is `Module.finrank` over `ZMod p`.
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), pp. 12, 21–22, 25–27, equations (2), (3). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

import Mathlib
import Definitions.Def_PrivPACLower_ICP_Supplement_Basics
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP.Supplement

/-! Grid points: `x : Fin N` stands for the integer `x + 1 ∈ [N] = {1, …, N}`. -/

/-- Axis-aligned boxes `B_{N,d}` on `[N]^d` (p. 21): indicators of `∏_j [a_j, b_j]`,
`1 ≤ a_j ≤ b_j ≤ N`. -/
def Boxes (N d : ℕ) : Set ((Fin d → Fin N) → Bool) :=
  {h | ∃ a b : Fin d → ℕ, (∀ j, 1 ≤ a j ∧ a j ≤ b j ∧ b j ≤ N) ∧
    ∀ x, (h x = true ↔ ∀ j, a j ≤ (x j).val + 1 ∧ (x j).val + 1 ≤ b j)}

/-- Unions of at most `k` intervals `I_{N,k}` on `[N]` (p. 22): `k` integer intervals
`[a_i, b_i]`, an interval with `a_i > b_i` being empty, so the empty union is included. -/
def Intervals (N k : ℕ) : Set (Fin N → Bool) :=
  {h | ∃ a b : Fin k → ℕ, ∀ x : Fin N, (h x = true ↔ ∃ i, a i ≤ x.val + 1 ∧ x.val + 1 ≤ b i)}

/-- Affine halfspaces `H_{N,d}` on `[N]^d` (p. 22): `x ↦ 1{⟨w, x⟩ ≤ θ}`, `w ∈ ℝ^d`, `θ ∈ ℝ`. -/
def Halfspaces (N d : ℕ) : Set ((Fin d → Fin N) → Bool) :=
  {h | ∃ (w : Fin d → ℝ) (θ : ℝ), ∀ x,
    (h x = true ↔ ∑ j, w j * (((x j).val : ℝ) + 1) ≤ θ)}

/-- Convex `k`-gons `C_{N,k}` on `[N]^2` (p. 22): indicators of intersections of at most `k`
closed real halfplanes `a z₁ + b z₂ ≤ c`, restricted to the grid (unbounded intersections
included; the degenerate rows `a = b = 0` give the whole plane or the empty set). -/
def Polygons (N k : ℕ) : Set ((Fin N × Fin N) → Bool) :=
  {h | ∃ a b c : Fin k → ℝ, ∀ z : Fin N × Fin N,
    (h z = true ↔ ∀ i, a i * ((z.1.val : ℝ) + 1) + b i * ((z.2.val : ℝ) + 1) ≤ c i)}

/-- `Line_p` (p. 25): the `p²` functions `f_{a,b}(x, y) = 1{y = a x + b}` on `ℤ_p²`. -/
def Line (p : ℕ) : Set ((ZMod p × ZMod p) → Bool) :=
  {h | ∃ a b : ZMod p, ∀ z, (h z = true ↔ z.2 = a * z.1 + b)}

/-- `S_{d,D}` (p. 26): membership indicators of the linear subspaces `V ⊆ 𝔽_p^D`, `dim V ≤ d`. -/
def Subspaces (p d D : ℕ) : Set ((Fin D → ZMod p) → Bool) :=
  {h | ∃ V : Submodule (ZMod p) (Fin D → ZMod p), Module.finrank (ZMod p) V ≤ d ∧
    ∀ x, (h x = true ↔ x ∈ V)}

/-- The nodes `X_k` of the complete binary tree of depth `k` (p. 27): binary strings of length
at most `k`, the root being the empty string. -/
abbrev TreeNodes (k : ℕ) := {u : List Bool // u.length ≤ k}

/-- `Path_k` (p. 27): `h_s(u) = 1{u ⪯ s}` for the leaves `s ∈ {0,1}^k`. -/
def Path (k : ℕ) : Set (TreeNodes k → Bool) :=
  {h | ∃ s : List Bool, s.length = k ∧ ∀ u : TreeNodes k, (h u = true ↔ u.1 <+: s)}

/-- `T_{d,k}` (p. 27): on `X_{2k}`, `h_A(u) = 1{u ⪯ s for some s ∈ A}`, `A ⊆ {0,1}^{2k}`,
`|A| ≤ d`. -/
def PathUnion (d k : ℕ) : Set (TreeNodes (2 * k) → Bool) :=
  {h | ∃ A : Finset (List Bool), A.card ≤ d ∧ (∀ s ∈ A, s.length = 2 * k) ∧
    ∀ u : TreeNodes (2 * k), (h u = true ↔ ∃ s ∈ A, u.1 <+: s)}

/-- Admissible block lengths (p. 12): `r_i ∈ {⌊D/v⌋, ⌈D/v⌉}` with `∑ r_i = D`. -/
def AdmissibleBlocks (v D : ℕ) (r : Fin v → ℕ) : Prop :=
  (∀ i, r i = ⌊(D : ℚ) / v⌋₊ ∨ r i = ⌈(D : ℚ) / v⌉₊) ∧ ∑ i, r i = D

/-- The product class `P_{v,D}` of (2), p. 12, on `X_P = ⋃_i {i} × [N_i]`, `N_i = 2^{r_i}`. -/
def ProductClass (v : ℕ) (r : Fin v → ℕ) : Set ((Σ i : Fin v, Fin (2 ^ r i)) → Bool) :=
  {h | ∃ t : Fin v → ℕ, (∀ i, t i ≤ 2 ^ r i) ∧
    ∀ z : Σ i : Fin v, Fin (2 ^ r i), (h z = true ↔ z.2.val + 1 ≤ t z.1)}

/-- The union class `U_{v,D} = F_v ∪ Thr_{2^D − 1}` of (3), p. 12, on `A ⊔ B`, `|A| = v`,
`B = [2^D − 1]`: all labelings of `A` extended by zero on `B`, and the thresholds on `B`
extended by zero on `A`. -/
def UnionClass (v D : ℕ) : Set ((Fin v ⊕ Fin (2 ^ D - 1)) → Bool) :=
  {h | (∃ f : Fin v → Bool, ∀ z, h z = Sum.elim f (fun _ => false) z) ∨
    (∃ t : ℕ, t ≤ 2 ^ D - 1 ∧
      ∀ z, h z = Sum.elim (fun _ => false) (fun x : Fin (2 ^ D - 1) => decide (x.val + 1 ≤ t)) z)}

/-- `L_P = log*(max{2, D/v})` (p. 12), real division. -/
noncomputable def LP (v D : ℕ) : ℕ := logStar (max 2 ((D : ℝ) / v))

/-- `L_U = log*(max{2, D})` (p. 12). -/
noncomputable def LU (D : ℕ) : ℕ := logStar (max 2 (D : ℝ))

end PrivPACLower.ICP.Supplement


