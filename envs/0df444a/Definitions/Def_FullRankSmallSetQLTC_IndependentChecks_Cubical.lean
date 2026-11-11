-- Prove2me | Definitions.Def_FullRankSmallSetQLTC_IndependentChecks_Cubical
-- name    : FullRankSmallSetQLTC_IndependentChecks_Cubical
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:06:12.36895+00:00
-- url     : https://prove2.me/theorems/b51d12e6-5aab-4b8f-9ebf-b59c8f623372
-- title:
--   Decorated cubical complexes, signatures, incidence graphs and the line product
-- statement:
--   Let $G$ be a group.
--
--   1. Inverse-closed $A_1,\dots,A_h\subseteq G$ are **cubical generating sets** if $A_iA_j=A_jA_i$ ($i\ne j$) and $|A_1\cdots A_h|=\prod_i|A_i|$.
--   2. The **decorated Cayley cubical complex** $Y=\mathrm{Cay}(G;A_1,\dots,A_h)$ on $G\times\mathbb F_2^h$ has as cubes the families $f=(f_x)_{x\in\mathbb F_2^h}$ with $f_x^{-1}f_{x+e_i}\in A_i$. The **signature** of $f$ is $(x,i)\mapsto f_x^{-1}f_{x+e_i}$; the normalized cube of a signature $\sigma$ is $\phi_\sigma(x)=f_0^{-1}f_x$.
--   3. The complex is **$\alpha$-expanding** (§4.2) if for every nonempty $I\subseteq[h]$ the operator $(T_If)(g)=\sum_{a\in A_I}f(ga)$ on $\ell^2(G)$, $A_I=\prod_{i\in I}A_i$, has norm at most $\alpha\sqrt{d_I}$, $d_I=\prod_{i\in I}|A_i|$, on the orthogonal complement of the constants.
--   4. The **Hadamard code** $H\subseteq\mathbb F_2^h$, $h=2^k$: the words $z\mapsto\langle y,\mathrm{bin}(z)\rangle$, $y\in\mathbb F_2^k$.
--   5. **Incidence graphs and the line product** (pp. 13–15). With cube sides $L=G\times S_L$, $R=G\times S_R$ and middle vertices $M=G\times H$, the cube $(g,\sigma)$ is adjacent to $(g\phi_\sigma(x),x)$, $x\in H$, and the middle vertex $u=(g,x)$ has the $\sigma$-neighbour $\mathrm{Nbr}_u(\sigma)=(g\phi_\sigma(x)^{-1},\sigma)$. Given binary matrices $C_x\in\mathbb F_2^{S_R\times S_L}$, the line product has an edge $\mathrm{LNbr}_u(\sigma)\sim\mathrm{RNbr}_u(\tau)$ for every $u$ of type $x$ and every $(\sigma,\tau)$ with $(C_x)_{\tau\sigma}=1$. The file defines its edge multiplicities, its simple graph, the subgraph of edges witnessed at type $x$, its binary adjacency map (multiplicities mod 2), simplicity, and the **distinct-witness condition** (3.2): a left cube and a right cube share at most one middle vertex.
--   6. The unmodified gadget family $C_x=C$ and the modified one $C^+_0=C+F$, $C^+_x=C$ ($x\ne0$).
--   7. Codes for polynomial-time statements: signature tables listed by the normal-form codes of $G_m$, and row-major gadget tables.
--
--   **Formalization Note** Signature sets are given as families of signatures indexed by finite types (injective where the source has sets). $\phi_\sigma$ is computed from a chosen cube of signature $\sigma$ (the source shows it depends only on $\sigma$). Expansion uses the source's equivalent operator-norm form, for complex-valued functions.
-- source:
--   Yali Aharon Holzman, Michael Ilan, Assaf Reiner, Amnon Ta-Shma, Full-Rank Constructions of Explicit Lossless Expanders and Good Small-Set qLTCs, STOC 2027 submission #692 (October 2026), §3.1, pp. 13–14; §3.3, p. 15; §3.4, p. 17; §4.2, p. 22 (printed page = PDF page)

import Mathlib
import Definitions.Def_FullRankSmallSetQLTC_IndependentChecks_Graph
import Definitions.Def_FullRankSmallSetQLTC_IndependentChecks_Quaternion

set_option autoImplicit false

namespace FullRankSmallSetQLTC.IndependentChecks

open Pointwise

/-! # Cubical complexes, signatures, incidence graphs and the line product (§§3.1, 4.2)

Cube vertices `x ∈ 𝔽₂^h` are `Fin h → ZMod 2`; `e_i` is `Pi.single i 1`. -/

section Complex

variable {G : Type*} [Group G] {h : ℕ}

/-- §3.1, p. 13: inverse-closed subsets `A₁, …, A_h ⊆ G` are **cubical generating sets** if
`A_iA_j = A_jA_i` for `i ≠ j` and `|A₁ ⋯ A_h| = ∏ |A_i|` (product sets in the order `1, …, h`). -/
def IsCubicalGenSet (A : Fin h → Set G) : Prop :=
  (∀ i, ∀ a ∈ A i, a⁻¹ ∈ A i) ∧
  (∀ i j, i ≠ j → A i * A j = A j * A i) ∧
  ((List.ofFn A).prod).ncard = ∏ i, (A i).ncard

/-- A cube of the decorated Cayley cubical complex `Cay(G; A₁, …, A_h)` on `G × 𝔽₂^h`: a family
`f = (f_x)_{x ∈ 𝔽₂^h}` with `f_x⁻¹ f_{x+e_i} ∈ A_i` for all `x` and `i`. -/
def IsCube (A : Fin h → Set G) (f : (Fin h → ZMod 2) → G) : Prop :=
  ∀ (x : Fin h → ZMod 2) (i : Fin h), (f x)⁻¹ * f (x + Pi.single i 1) ∈ A i

/-- Labelings `(x, i) ↦ σ(x, i)` of the directed edges of the cube. -/
abbrev Sig (G : Type*) (h : ℕ) := (Fin h → ZMod 2) → Fin h → G

/-- The signature of `f`: `(x, i) ↦ f_x⁻¹ f_{x+e_i}`. -/
def signature (f : (Fin h → ZMod 2) → G) : Sig G h :=
  fun x i => (f x)⁻¹ * f (x + Pi.single i 1)

/-- `σ` is a signature of the complex: the signature of some cube. -/
def IsSignature (A : Fin h → Set G) (σ : Sig G h) : Prop :=
  ∃ f, IsCube A f ∧ signature f = σ

open Classical in
/-- `ϕ_σ(x) = f₀⁻¹ f_x` for any cube `f` of signature `σ` (p. 13: it depends only on `σ`); the
unique cube of signature `σ` with `ϕ_σ(0) = 1`. Set to the constant `1` if `σ` is not a
signature. -/
noncomputable def normCube (A : Fin h → Set G) (σ : Sig G h) : (Fin h → ZMod 2) → G :=
  if hσ : IsSignature A σ then fun x => (hσ.choose 0)⁻¹ * hσ.choose x else fun _ => 1

/-- `A_I = ∏_{i ∈ I} A_i`, the product set in increasing order of `I`. -/
def prodSet (A : Fin h → Set G) (I : Finset (Fin h)) : Set G :=
  ((I.sort (· ≤ ·)).map A).prod

variable [Fintype G]

/-- §4.2, p. 22: the complex `Cay(G; A₁, …, A_h)` is `α`-**expanding** if for every nonempty
`I ⊆ [h]` the operator `(T_I f)(g) = Σ_{a ∈ A_I} f(ga)` on `ℓ²(G)` has norm at most `α √d_I` on
the orthogonal complement of the constants, `d_I = ∏_{i∈I} |A_i|` (the source's equivalent form
of the bound on the second eigenvalue of the graphs between types `y` and `y + 1_I`). -/
def IsExpanding (A : Fin h → Set G) (α : ℝ) : Prop :=
  ∀ I : Finset (Fin h), I.Nonempty → ∀ f : G → ℂ, ∑ g, f g = 0 →
    Real.sqrt (∑ g, ‖∑ᶠ (a : G) (_ : a ∈ prodSet A I), f (g * a)‖ ^ 2) ≤
      α * Real.sqrt (∏ i ∈ I, ((A i).ncard : ℝ)) * Real.sqrt (∑ g, ‖f g‖ ^ 2)

end Complex

/-! ## The Hadamard type set -/

/-- The Hadamard code `H ⊆ 𝔽₂^h` for `h = 2^k`: the words `z ↦ ⟨y, bin(z)⟩`, `y ∈ 𝔽₂^k`, where
`bin(z) ∈ 𝔽₂^k` are the binary digits of `z ∈ [0, 2^k)`. It has `h` elements, contains `0`, and
distinct elements are at Hamming distance `h/2` (for `k ≥ 1`). -/
def hadamard (k : ℕ) : Finset (Fin (2 ^ k) → ZMod 2) :=
  Finset.univ.image fun y : Fin k → ZMod 2 =>
    fun z : Fin (2 ^ k) => ∑ j : Fin k, y j * (if z.val.testBit j.val then 1 else 0)

/-! ## Incidence graphs and the line product (p. 13–15)

The two complexes have dimension `h = 2^k` and the same group `G`. Their cube sides are
`L = G × S_L`, `R = G × S_R` (signature sets indexed by `ιL`, `ιR`, through normalized cubes
`ϕL σ = ϕ^L_σ`, `ϕR τ = ϕ^R_τ`), and the middle vertices `M = G × H`. The cube `(g, σ)` is
adjacent to the middle vertex `(gϕ_σ(x), x)` for every `x ∈ H`, and a middle vertex `u = (g, x)`
has the unique `σ`-neighbour `Nbr_u(σ) = (gϕ_σ(x)⁻¹, σ)`. With a binary gadget matrix
`C_x ∈ 𝔽₂^{S_R × S_L}` at middle vertices of type `x`, the line product has an edge
`LNbr_u(σ) ∼ RNbr_u(τ)` for every `u` of type `x` and every `(σ, τ)` with `(C_x)_{τσ} = 1`. -/

section LineProduct

variable {G : Type*} [Group G] {k : ℕ} {ιL ιR : Type*}
  (ϕL : ιL → (Fin (2 ^ k) → ZMod 2) → G) (ϕR : ιR → (Fin (2 ^ k) → ZMod 2) → G)

open Classical in
/-- The number of middle neighbours shared by the cube `(gℓ, σ)` of `I_L` and the cube
`(gr, τ)` of `I_R`: `|N_{I_L}(ℓ) ∩ N_{I_R}(r)| = #{x ∈ H : gℓ ϕ^L_σ(x) = gr ϕ^R_τ(x)}`. -/
noncomputable def sharedMiddle (ℓ : Cell G ιL) (r : Cell G ιR) : ℕ :=
  ((hadamard k).filter fun x => ℓ.grp * ϕL ℓ.lab x = r.grp * ϕR r.lab x).card

/-- The distinct-witness condition (3.2), p. 14: `|N_{I_L}(ℓ) ∩ N_{I_R}(r)| ≤ 1` for all
`ℓ ∈ L`, `r ∈ R`. -/
def DistinctWitness : Prop :=
  ∀ (ℓ : Cell G ιL) (r : Cell G ιR), sharedMiddle ϕL ϕR ℓ r ≤ 1

variable (C : (Fin (2 ^ k) → ZMod 2) → Matrix ιR ιL (ZMod 2))

open Classical in
/-- The multiplicity of the line-product edge between `ℓ = (gℓ, σ)` and `r = (gr, τ)`: the
number of witnesses `u = (g, x)`, `x ∈ H`, with `LNbr_u(σ) = ℓ`, `RNbr_u(τ) = r` and
`(C_x)_{τσ} = 1`. Here `LNbr_u(σ) = ℓ` forces `g = gℓ ϕ^L_σ(x)`, so a witness of type `x`
exists iff `gℓ ϕ^L_σ(x) ϕ^R_τ(x)⁻¹ = gr`. -/
noncomputable def lpMult (ℓ : Cell G ιL) (r : Cell G ιR) : ℕ :=
  ((hadamard k).filter fun x =>
    ℓ.grp * ϕL ℓ.lab x * (ϕR r.lab x)⁻¹ = r.grp ∧ C x r.lab ℓ.lab = 1).card

/-- The line product `Z(I_L, I_R; (C_x)_x)` as a bipartite graph on `L ⊔ R`: `ℓ ∼ r` iff there
is at least one witness. -/
def lpAdj (ℓ : Cell G ιL) (r : Cell G ιR) : Prop :=
  0 < lpMult ϕL ϕR C ℓ r

/-- The edges of the line product witnessed at a middle vertex of type `x`. -/
def lpAdjAt (x : Fin (2 ^ k) → ZMod 2) (ℓ : Cell G ιL) (r : Cell G ιR) : Prop :=
  x ∈ hadamard k ∧ ℓ.grp * ϕL ℓ.lab x * (ϕR r.lab x)⁻¹ = r.grp ∧ C x r.lab ℓ.lab = 1

/-- The binary adjacency map `A_C : 𝔽₂^L → 𝔽₂^R` of the line product (multiplicities modulo 2). -/
noncomputable def lpMatrix : Matrix (Cell G ιR) (Cell G ιL) (ZMod 2) :=
  Matrix.of fun r ℓ => (lpMult ϕL ϕR C ℓ r : ZMod 2)

/-- The line product is simple: every pair has at most one witness. -/
def IsSimpleLP : Prop :=
  ∀ (ℓ : Cell G ιL) (r : Cell G ιR), lpMult ϕL ϕR C ℓ r ≤ 1

end LineProduct

/-! ## Gadgets and the modified gadget family -/

/-- The unmodified gadget family: `C_x = C` at every middle type. -/
def constGadget {k : ℕ} {ιL ιR : Type*} (C : Matrix ιR ιL (ZMod 2)) :
    (Fin (2 ^ k) → ZMod 2) → Matrix ιR ιL (ZMod 2) :=
  fun _ => C

open Classical in
/-- §3.4, p. 17: the modified gadget family `C₀⁺ = C + F`, `C_x⁺ = C` for `x ≠ 0`. -/
noncomputable def plusGadget {k : ℕ} {ιL ιR : Type*} (C F : Matrix ιR ιL (ZMod 2)) :
    (Fin (2 ^ k) → ZMod 2) → Matrix ιR ιL (ZMod 2) :=
  fun x => if x = 0 then C + F else C

/-! ## Encodings for polynomial-time statements over `G_m` -/

/-- The binary digits of `z` as a cube vertex `x ∈ 𝔽₂^h`. -/
def bitsVec (h z : ℕ) : Fin h → ZMod 2 := fun j => if z.testBit j.val then 1 else 0

/-- The table of a signature `σ` on `G_m`: the codes `nfCode σ(x, i)`, listing `x = bitsVec z`
for `z = 0, …, 2^h − 1` and, for each, `i = 0, …, h − 1`. -/
noncomputable def sigCode (m h : ℕ) (σ : Sig ↥(Gm m) h) : List ℕ :=
  (List.range (2 ^ h)).flatMap fun z =>
    (List.finRange h).map fun i => nfCode m ((σ (bitsVec h z) i : ↥(Gm m)) : GHat m)

open Classical in
/-- The adjacency table of a gadget `S_L ⊔ S_R` with `S_L = [a]`, `S_R = [b]`: row-major
`0/1` entries. -/
noncomputable def gadgetCode {a b : ℕ} (gad : Fin a → Fin b → Prop) : List ℕ :=
  (List.finRange a).flatMap fun i => (List.finRange b).map fun j => if gad i j then 1 else 0

end FullRankSmallSetQLTC.IndependentChecks


