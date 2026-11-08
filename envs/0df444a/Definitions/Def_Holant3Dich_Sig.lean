-- Prove2me | Definitions.Def_Holant3Dich_Sig
-- name    : Holant3Dich_Sig
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:38:43.131298+00:00
-- url     : https://prove2.me/theorems/dbc931d1-a9c0-40eb-ba06-90770bc5bb36
-- title:
--   Signatures on a finite domain, tensor powers, $\mathrm{Sym}$, holographic action, contraction and restriction
-- statement:
--   A **signature** of arity $r$ on the domain $\{0,\dots,q-1\}$ is a function $F:\{0,\dots,q-1\}^r\to\mathbb C$. The domain $\{\mathsf B,\mathsf G,\mathsf R\}$ of the paper is $q=3$ with $\mathsf B=0$, $\mathsf G=1$, $\mathsf R=2$; the Boolean domain is $q=2$.
--
--   1. $F$ is **symmetric** if $F(x_{\sigma(1)},\dots,x_{\sigma(r)})=F(x_1,\dots,x_r)$ for every permutation $\sigma$.
--   2. $F$ is **degenerate** if $F=c\,u_1\otimes\cdots\otimes u_r$ for vectors $u_i\in\mathbb C^q$ and a scalar $c$ (a signature and its nonzero multiples are identified, p.13).
--   3. For $u\in\mathbb C^q$, $u^{\otimes n}(x)=\prod_i u(x_i)$, and $\mathrm{Sym}(u,\dots,u,v)$ of order $n$ is the sum of the $n$ tensor products with $v$ in exactly one position, with no normalizing factor.
--   4. For a $q\times q$ matrix $M$, the **holographic action** is $(M^{\otimes n}F)(x)=\sum_y\prod_i M_{x_i y_i}\,F(y)$ (column-vector convention); on a binary signature with matrix $F$ it is $MFM^{\mathsf T}$.
--   5. $\langle F,u\rangle(x)=\sum_c u(c)F(x,c)$ connects the unary $u$ to the last input of $F$; repeated connection of $u_1,u_2,\dots$ is `contractMany`.
--   6. $F^{*\to\{i,j\}}$ restricts a domain-3 signature to inputs in $\{i,j\}$, identifying $i$ with $0$ and $j$ with $1$.
--   7. The matrix of a binary signature has entry $(i,j)$ equal to $F(i,j)$, and $[x_0,\dots,x_n]$ lists a symmetric Boolean signature by Hamming weight.
--
--   These are the objects of §§2.1–2.3 (pp.11–14) on which every statement of the mission is built.
--
--   **Formalization Note** A signature is a dependent pair (arity, value function). With the scalar in the definition of degeneracy, every nullary and every unary signature is degenerate, so a nondegenerate signature has arity at least 2. Contraction is applied only to signatures of positive arity.
-- source:
--   Cai, Ihm, Group Action and Spin Representation Lead to a Holant* Complexity Dichotomy on Domain Size 3, STOC 2027 submission, arXiv:2610.04750 (held manuscript sha256 b608db44…), §2.1 p.11, §2.2 p.12, §2.3 pp.12–14

import Mathlib

set_option autoImplicit false

namespace Holant3Dich

/-- A **signature** on the domain `Fin q`: an arity `r` together with a function
`(Fin q)^r → ℂ`. Cai–Ihm, *Group Action and Spin Representation Lead to a Holant\* Complexity
Dichotomy on Domain Size 3*, STOC 2027 submission, arXiv:2610.04750 (held manuscript sha256
b608db44…), §2.1, p.11: "Let D be a finite domain set, and F be a set of constraint functions,
called signatures. Each F ∈ F is a mapping D^k → C for some arity k."

**Formalization Note.** The domain {B, G, R} is `Fin 3` with B = 0, G = 1, R = 2 (p.14); the
Boolean domain {0, 1} is `Fin 2`. -/
abbrev Sig (q : ℕ) := Σ r : ℕ, (Fin r → Fin q) → ℂ

variable {q : ℕ}

/-- `F` is **symmetric**: invariant under every permutation of its inputs. Cai–Ihm, §2.3, p.13:
"A signature F of arity k is symmetric if F(x1, …, xk) = F(xσ(1), …, xσ(k)) for all σ ∈ Sk". -/
def Sig.IsSymmetric (F : Sig q) : Prop :=
  ∀ (σ : Equiv.Perm (Fin F.1)) (x : Fin F.1 → Fin q), F.2 (x ∘ σ) = F.2 x

/-- `F` is **degenerate**: a scalar multiple of a tensor product `u₁ ⊗ ⋯ ⊗ u_k` of unary
signatures. Cai–Ihm, §2.1, p.11: "A signature F of arity k is degenerate if F = u1 ⊗ · · · ⊗ uk
for some vectors ui"; p.13: "We consider a signature F and its nonzero multiple cF as the same
signature".

**Formalization Note.** The scalar `c` changes nothing for arity `k ≥ 1` (absorb it into `u₁`);
it makes every nullary signature degenerate, in line with p.13. The zero signature and every
unary signature are degenerate. -/
def Sig.IsDegenerate (F : Sig q) : Prop :=
  ∃ (c : ℂ) (u : Fin F.1 → Fin q → ℂ), ∀ x, F.2 x = c * ∏ i, u i (x i)

/-- Every value of `F` is algebraic over `ℚ`. -/
def Sig.IsAlgebraicSig (F : Sig q) : Prop := ∀ x, IsAlgebraic ℚ (F.2 x)

/-- Every value of every member of the list `L` is algebraic over `ℚ`. -/
def AlgList {u : ℕ} (L : Fin u → Sig q) : Prop := ∀ i, (L i).IsAlgebraicSig

/-- Every value of every member of the list `L` lies in the subfield `K ⊆ ℂ`. -/
def EntriesIn {u : ℕ} (L : Fin u → Sig q) (K : IntermediateField ℚ ℂ) : Prop :=
  ∀ i x, (L i).2 x ∈ K

/-- The tensor power `u^{⊗n}`: `x ↦ ∏ᵢ u(xᵢ)`. Cai–Ihm, §2.1, p.11: "We write u⊗k for
u ⊗ · · · ⊗ u with k copies of u." -/
def tpow (u : Fin q → ℂ) (n : ℕ) : (Fin n → Fin q) → ℂ := fun x => ∏ i, u (x i)

/-- `Sym(u, …, u, v)` of order `n`: the sum of the `n` tensor products with `v` in exactly one
position and `u` in the others, with no normalizing factor. Cai–Ihm, §2.3, p.13:
"Sym(u, . . . , u, v) = (u ⊗ · · · ⊗ u ⊗ v) + (u ⊗ · · · ⊗ u ⊗ v ⊗ u) + · · · + (v ⊗ u ⊗ · · · ⊗ u),
the sum of k terms where v is moving from right to left. … Note that there is no normalizing
factor, and we are not summing up over all possible permutations." -/
def symUV (u v : Fin q → ℂ) (n : ℕ) : (Fin n → Fin q) → ℂ :=
  fun x => ∑ j : Fin n, ∏ i, (if i = j then v else u) (x i)

/-- The holographic action of a `q × q` matrix `M` on an arity-`n` tensor viewed as a column
vector: `M^{⊗n} f`, i.e. `(M^{⊗n} f)(x) = Σ_y ∏ᵢ M(xᵢ, yᵢ) f(y)`. Cai–Ihm, §2.2, p.12:
"TF = {G : ∃F ∈ F of arity n, such that G = T^{⊗n}F} … Whenever we write T^{⊗n}F or TF, we view
the signatures as column vectors". For a binary `f` with matrix `F` this is `M F Mᵀ`. -/
def actT (M : Matrix (Fin q) (Fin q) ℂ) {n : ℕ} (f : (Fin n → Fin q) → ℂ) :
    (Fin n → Fin q) → ℂ :=
  fun x => ∑ y : Fin n → Fin q, (∏ i, M (x i) (y i)) * f y

/-- The holographic action `M F = M^{⊗n} F` on a signature (the arity is kept). -/
def act (M : Matrix (Fin q) (Fin q) ℂ) (F : Sig q) : Sig q := ⟨F.1, actT M F.2⟩

/-- `⟨f, u⟩`: the arity-`(n-1)` gadget obtained by connecting the unary `u` to the last input of
`f`: `⟨f, u⟩(x) = Σ_c u(c) f(x, c)`. Cai–Ihm, §2.3, p.14: "Let u ∈ C^{|D|} and F be a symmetric
signature on domain D of arity k. Then, ⟨F, u⟩ is the arity k − 1 gadget obtained by connecting u
to any edge of F. Since F is symmetric, the choice of the edge does not matter."

**Formalization Note.** Used only for arity `n ≥ 1`; the last input is the one connected. -/
def contractT {n : ℕ} (f : (Fin n → Fin q) → ℂ) (u : Fin q → ℂ) :
    (Fin (n - 1) → Fin q) → ℂ :=
  fun x => ∑ c : Fin q, u c * f (fun i => if h : i.val < n - 1 then x ⟨i.val, h⟩ else c)

/-- `⟨F, u⟩` on a signature. -/
def Sig.contract (F : Sig q) (u : Fin q → ℂ) : Sig q := ⟨F.1 - 1, contractT F.2 u⟩

/-- Connecting the unaries `u₁, u₂, …` one after another (each to the last remaining input).
Cai–Ihm, Prop. 9.10, p.90: "connecting u1, . . . , uk to F". -/
def Sig.contractMany (F : Sig q) (us : List (Fin q → ℂ)) : Sig q := us.foldl Sig.contract F

/-- The domain restriction `F^{*→{i,j}}` of a domain-3 signature to a Boolean signature, with
`i ↦ 0` and `j ↦ 1`. Cai–Ihm, §2.3, p.14: "we use the symbol F^{∗→{i,j}} to denote the Boolean
domain signature obtained by restricting the inputs of F to be from {i, j} ⊆ {B, G, R} … F^{∗→{BG}}
is viewed as identifying B as 0 and G as 1." -/
def restrict (i j : Fin 3) (F : Sig 3) : Sig 2 :=
  ⟨F.1, fun x => F.2 (fun t => if x t = 0 then i else j)⟩

/-- The matrix `M_F` of a binary signature, `(i, j) ↦ F(i, j)`. Cai–Ihm, §2.3, p.13: "A binary
signature F (not necessarily symmetric) can be expressed as a |D| × |D| matrix MF, where the entry
(i, j) ∈ D × D is the value F(i, j)."

**Formalization Note.** Meaningful only for arity 2 (input 0 is the row index, input 1 the
column index); it is applied only to binary signatures. -/
def Sig.toMatrix (F : Sig q) : Matrix (Fin q) (Fin q) ℂ :=
  fun i j => F.2 (fun t => if t.val = 0 then i else j)

/-- The binary signature of a matrix, `(x₀, x₁) ↦ M(x₀, x₁)`. -/
def binSig (M : Matrix (Fin q) (Fin q) ℂ) : Sig q := ⟨2, fun x => M (x 0) (x 1)⟩

/-- The value `x_k` of a symmetric Boolean signature `[x₀, x₁, …, x_n]` on inputs of Hamming
weight `k` (taken at the input whose first `k` entries are `1`). Cai–Ihm, §2.3, p.13: "A
symmetric signature F on k Boolean variables {0, 1} can be expressed as [f0, f1, . . . , fk] where
fi is the value of F on inputs of Hamming weight i." -/
def boolVal (F : Sig 2) (k : ℕ) : ℂ := F.2 (fun t => if t.val < k then 1 else 0)

end Holant3Dich


