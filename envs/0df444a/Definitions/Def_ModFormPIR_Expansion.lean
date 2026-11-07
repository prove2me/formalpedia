-- Prove2me | Definitions.Def_ModFormPIR_Expansion
-- name    : ModFormPIR_Expansion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:58:42.478196+00:00
-- url     : https://prove2.me/theorems/d8186f0c-0ed3-4e6e-829d-650da772bff8
-- title:
--   Quadratic-phase delta expansions, $S_d(\vartheta,\nu)$, and the scheme of Fig. 5
-- statement:
--   Let $\gamma$ be a primitive $q$-th root of unity in a field $\mathbb F$. Coefficients $c_{w,t}\in\mathbb F$ ($w\in\mathbb Z_q^d$, $t\in\mathbb Z_q$) form a **quadratic-phase delta expansion** if
--   $$\sum_{t\in\mathbb Z_q}\sum_{w\in\mathbb Z_q^d}c_{w,t}\,\gamma^{\langle w,x\rangle+t\langle x,x\rangle}=\begin{cases}1&x=0\\0&x\ne0\end{cases}$$
--   for every $x\in\mathbb Z_q^d$. It has **support** in $\mathcal W\times\mathcal A$ if $c_{w,t}\ne0$ forces $(w,t)\in\mathcal W\times\mathcal A$, and is **$(k,s)$-sparse** if moreover $|\mathcal W|\le k$, $|\mathcal A|\le s$. It is **symmetric** if $c_{a,t}=c_{a',t}$ whenever $a,a'$ are permutations of each other.
--
--   For a feasible pair with budget $\gamma(\vartheta,\nu)$, the sets of Definition 12.1 are $S^{\mathrm{sq}}_d(\nu)=\{z:\sum_iw_q(z_i)\le\nu d\}$, $S^{\mathrm{edge}}_d(\vartheta,\nu)=\{z:\sum_iw_{q,\vartheta}(z_i)\le\gamma d\}$, $T_d=\{uz+b\mathbf 1\}$ over units $u$, $b\in\mathbb Z_q$, $z$ in their union, and $S_d=\{z+ce_i:z\in T_d\}$.
--
--   The file also defines the scheme of Fig. 5: tables $f_t(x)=\sum_v\mathrm{DB}_v\gamma^{\langle x,v\rangle+t\langle v,v\rangle}$, queries $\mathrm{qu}_t=r-2t\,i$, and the record (17), and straight-line programs over a ring, which measure "operations" in Theorem 7.1.
--
--   **Formalization Note** $\gamma^a$ for $a\in\mathbb Z_q$ is `γ ^ a.val`. A straight-line program has input, constant, sum and product gates, each costing one.
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), Definition 4.3, (13), p.19; Lemma 9.1, p.33; Definition 12.1, p.66; Fig. 5, p.27; (17), p.28

import Mathlib
import Definitions.Def_ModFormPIR_Exponent

open Matrix
open scoped BigOperators

set_option autoImplicit false

namespace ModFormPIR

/-!
# Quadratic-phase delta expansions, the sets `S_d(ϑ,ν)`, Fig. 5, and straight-line programs

Henzinger, Ragavan, *Doubly-Efficient Private Information Retrieval from Modular Forms*, STOC 2027
submission (manuscript sha256 2442f3db…), Definition 4.3 with (13), p.19; Lemma 9.1, p.33; Definition 12.1,
p.66; Fig. 5, p.27, and (17), p.28.

**Formalization Note.** `γ` is a primitive `q`-th root of unity in the field (Definition 4.1), and `γ^a` for
`a ∈ ℤ_q` is `γ ^ a.val`. "Operations over `𝔽_p`" in Theorem 7.1 are read as gates of a straight-line program
(`Gate`): an input, a constant, a sum or a product, each costing one gate.
-/

variable {𝔽 : Type*} [Field 𝔽] {q d : ℕ} [NeZero q]

/-- Definition 4.3, (13): `∑_t ∑_w c_{w,t} γ^{⟨w,x⟩ + t⟨x,x⟩}` is `1` at `x = 0` and `0` elsewhere. -/
def IsDeltaExpansion (γ : 𝔽) (c : (Fin d → ZMod q) → ZMod q → 𝔽) : Prop :=
  ∀ x : Fin d → ZMod q,
    ∑ t : ZMod q, ∑ w : Fin d → ZMod q, c w t * γ ^ (w ⬝ᵥ x + t * (x ⬝ᵥ x)).val =
      if x = 0 then 1 else 0

/-- Definition 4.3: the support of `c` is contained in `𝒲 × 𝒜`. -/
def HasSupport (c : (Fin d → ZMod q) → ZMod q → 𝔽) (𝒲 : Set (Fin d → ZMod q))
    (𝒜 : Set (ZMod q)) : Prop :=
  ∀ w t, c w t ≠ 0 → w ∈ 𝒲 ∧ t ∈ 𝒜

/-- Definition 4.3: `c` is `(k, s)`-sparse, i.e. supported on some `𝒲 × 𝒜` with `|𝒲| ≤ k`, `|𝒜| ≤ s`. -/
def IsSparse (c : (Fin d → ZMod q) → ZMod q → 𝔽) (k s : ℕ) : Prop :=
  ∃ (𝒲 : Finset (Fin d → ZMod q)) (𝒜 : Finset (ZMod q)),
    HasSupport c (𝒲 : Set (Fin d → ZMod q)) (𝒜 : Set (ZMod q)) ∧ 𝒲.card ≤ k ∧ 𝒜.card ≤ s

/-- Lemma 9.1, p.33: `c` is symmetric, `c_{a,t} = c_{a',t}` when `a, a'` are permutations of each other. -/
def IsSymmetric (c : (Fin d → ZMod q) → ZMod q → 𝔽) : Prop :=
  ∀ (π : Equiv.Perm (Fin d)) (a : Fin d → ZMod q) (t : ZMod q), c (a ∘ π) t = c a t

/-- `𝒲` is invariant under permuting the `d` coordinates (p.19). -/
def IsPermInvariant (𝒲 : Set (Fin d → ZMod q)) : Prop :=
  ∀ (π : Equiv.Perm (Fin d)) (a : Fin d → ZMod q), a ∈ 𝒲 → a ∘ π ∈ 𝒲

/-- Definition 12.1: `S^sq_d(ν) = {z : ∑_i w_q(z_i) ≤ νd}`, with `w_q = w_{q,1/2}`. -/
def Ssq (q d : ℕ) (ν : ℝ) : Set (Fin d → ZMod q) :=
  {z | ∑ i, cost q (1 / 2) (z i) ≤ ν * d}

/-- Definition 12.1: `S^edge_d(ϑ,ν) = {z : ∑_i w_{q,ϑ}(z_i) ≤ γ(ϑ,ν) d}`. -/
def Sedge (q s d : ℕ) (ϑ ν : ℝ) : Set (Fin d → ZMod q) :=
  {z | ∑ i, cost q ϑ (z i) ≤ budget q s ϑ ν * d}

/-- Definition 12.1: `T_d(ϑ,ν) = {uz + b𝟏 : u ∈ ℤ_q^*, b ∈ ℤ_q, z ∈ S^sq_d(ν) ∪ S^edge_d(ϑ,ν)}`. -/
def Td (q s d : ℕ) (ϑ ν : ℝ) : Set (Fin d → ZMod q) :=
  {y | ∃ (u : (ZMod q)ˣ) (b : ZMod q), ∃ z ∈ Ssq q d ν ∪ Sedge q s d ϑ ν,
    y = fun i => (u : ZMod q) * z i + b}

/-- Definition 12.1: `S_d(ϑ,ν) = {z + c e_i : c ∈ ℤ_q, i ∈ [d], z ∈ T_d(ϑ,ν)}`. -/
def Sd (q s d : ℕ) (ϑ ν : ℝ) : Set (Fin d → ZMod q) :=
  {y | ∃ (c : ZMod q) (i : Fin d), ∃ z ∈ Td q s d ϑ ν, y = z + Pi.single i c}

/-- Fig. 5, Preprocess: `f_t(x) = ∑_v DB_v γ^{⟨x,v⟩ + t⟨v,v⟩}`. -/
def fig5Table (γ : 𝔽) (DB : (Fin d → ZMod q) → 𝔽) (t : ZMod q) (x : Fin d → ZMod q) : 𝔽 :=
  ∑ v : Fin d → ZMod q, DB v * γ ^ (x ⬝ᵥ v + t * (v ⬝ᵥ v)).val

/-- Fig. 5, Query: `qu_t = r - 2t·i`. -/
def fig5Query (r i : Fin d → ZMod q) (t : ZMod q) : Fin d → ZMod q :=
  fun j => r j - 2 * t * i j

/-- Fig. 5, Reconstruct, (17): `∑_{t∈𝒜} ∑_{w∈𝒲} c_{w,t} f_t(qu_t + w) γ^{⟨t·i - r - w, i⟩}`. -/
def fig5Record (γ : 𝔽) (c : (Fin d → ZMod q) → ZMod q → 𝔽) (𝒲 : Finset (Fin d → ZMod q))
    (𝒜 : Finset (ZMod q)) (DB : (Fin d → ZMod q) → 𝔽) (i r : Fin d → ZMod q) : 𝔽 :=
  ∑ t ∈ 𝒜, ∑ w ∈ 𝒲, c w t * fig5Table γ DB t (fig5Query r i t + w) *
    γ ^ ((fun j => t * i j - r j - w j) ⬝ᵥ i).val

/-- A gate of a straight-line program over `R` with inputs indexed by `ι`: an input, a constant, or the sum
or product of two earlier gates (by position). -/
inductive Gate (R ι : Type*) where
  | input (v : ι)
  | const (a : R)
  | add (i j : ℕ)
  | mul (i j : ℕ)

/-- The values of the gates of `gs` on input `inp`, in order. -/
def evalGates {R ι : Type*} [Semiring R] (inp : ι → R) (gs : List (Gate R ι)) : List R :=
  gs.foldl
    (fun vals g =>
      vals ++ [match g with
        | .input v => inp v
        | .const a => a
        | .add i j => vals.getD i 0 + vals.getD j 0
        | .mul i j => vals.getD i 0 * vals.getD j 0])
    []

/-- The straight-line program `gs` with output positions `out` computes `f`. -/
def ComputesBy {R ι κ : Type*} [Semiring R] (gs : List (Gate R ι)) (out : κ → ℕ)
    (f : (ι → R) → κ → R) : Prop :=
  ∀ (inp : ι → R) (y : κ), (evalGates inp gs).getD (out y) 0 = f inp y

/-- The type of `w`: how many coordinates take each value (Lemma 9.2, p.34). -/
def typeOf (w : Fin d → ZMod q) : ZMod q → ℕ :=
  fun j => (Finset.univ.filter fun i => w i = j).card

/-- `M_d = D! · q^{dD}` with `D = q²(d+1)^q` (Lemma 9.3). -/
def bigM (q d : ℕ) : ℕ :=
  Nat.factorial (q ^ 2 * (d + 1) ^ q) * q ^ (d * (q ^ 2 * (d + 1) ^ q))

end ModFormPIR


