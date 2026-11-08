-- Prove2me | Definitions.Def_Holant3Dich_TractType
-- name    : Holant3Dich_TractType
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:50:48.576361+00:00
-- url     : https://prove2.me/theorems/6ec414fe-94df-4ee6-aa5b-a6594fe943db
-- title:
--   The nine tractable types $\mathfrak A_3,\mathfrak A_2,\mathfrak B_3,\mathfrak B_2,\mathfrak C^0,\mathfrak C^1_2,\mathfrak C^1_s,\mathfrak C^1_z,\mathfrak C^1_g$ and their defining forms
-- statement:
--   Let $F$ be a nondegenerate symmetric signature of arity $n\ge3$ on $\{\mathsf B,\mathsf G,\mathsf R\}$. $F$ **is of type** $\tau$ if some $T\in O(3,\mathbb C)$ satisfies the condition of $\tau$; $F$ is **of the defining form** of $\tau$ if $T=I$ works (Definition 9.7, p.88):
--
--   1. $\mathfrak A_3$: $TF=a e_1^{\otimes n}+b e_2^{\otimes n}+c e_3^{\otimes n}$ with $a,b,c\neq0$.
--   2. $\mathfrak A_2$: $TF=a e_1^{\otimes n}+b e_2^{\otimes n}$ with $a,b\neq0$.
--   3. $\mathfrak B_3$: $TF=a\beta_+^{\otimes n}+b\beta_-^{\otimes n}+c e_3^{\otimes n}$ with $a,b,c\neq0$.
--   4. $\mathfrak B_2$: $TF=a\beta_+^{\otimes n}+b\beta_-^{\otimes n}$ with $a,b\neq0$.
--   5. $\mathfrak C^0$: $\langle TF,\beta_+\rangle=0$.
--   6. $\mathfrak C^1_2$: $Y^{-1}TF=a e_1^{\otimes n}+\lambda\,\mathrm{Sym}(e_1,\dots,e_1,e_2)$ with $\lambda\neq0$.
--   7. $\mathfrak C^1_s$: $Y^{-1}TF=a e_1^{\otimes n}+\lambda\,\mathrm{Sym}(e_1,\dots,e_1,e_2)+d e_3^{\otimes n}$ with $\lambda,d\neq0$.
--   8. $\mathfrak C^1_z$: the support of $Y^{-1}TF$ lies in the permutations of $\mathsf B^n,\mathsf B^{n-1}\mathsf G,\mathsf B^{n-1}\mathsf R,\mathsf B^{n-2}\mathsf R^2$, and $Y^{-1}TF(\mathsf B^{n-1}\mathsf G)\neq0$, $Y^{-1}TF(\mathsf B^{n-2}\mathsf R^2)\neq0$.
--   9. $\mathfrak C^1_g$: $Y^{-1}TF\in\mathcal C$ and $F$ is not of type $\mathfrak C^0,\mathfrak C^1_2,\mathfrak C^1_s$ or $\mathfrak C^1_z$.
--
--   Here $TF$ is the holographic action $T^{\otimes n}F$ and $Y^{-1}TF=(Y^{-1}T)^{\otimes n}F$. For $n=3$, types 1–8 are those of Definition 2.8 (p.18). The types sort the signatures that are tractable on their own and are the case split of the hardness proofs.
--
--   **Formalization Note** The type $\mathfrak C^1_g$ is used in its implicit form of Definition 9.7 for every arity, including $n=3$ (Corollary 3.13 relates it to the explicit ternary condition of Definition 2.8). Its exclusions are stated for $TF$; being of a type is invariant under orthogonal transformations. The supports of type $\mathfrak C^1_z$ are stated by the numbers of $\mathsf G$'s and $\mathsf R$'s in an input.
-- source:
--   Cai, Ihm, Group Action and Spin Representation Lead to a Holant* Complexity Dichotomy on Domain Size 3, STOC 2027 submission, arXiv:2610.04750 (held manuscript sha256 b608db44…), Definition 9.7 p.88; Definition 2.8 p.18

import Mathlib
import Definitions.Def_Holant3Dich_Sig
import Definitions.Def_Holant3Dich_IsOrth3
import Definitions.Def_Holant3Dich_InC

set_option autoImplicit false

namespace Holant3Dich

/-- The nine tractable types `𝔄₃, 𝔄₂, 𝔅₃, 𝔅₂, ℭ⁰, ℭ¹₂, ℭ¹ₛ, ℭ¹_z, ℭ¹_g` of Definition 9.7.
Cai–Ihm, *Group Action and Spin Representation Lead to a Holant\* Complexity Dichotomy on Domain
Size 3*, STOC 2027 submission, arXiv:2610.04750 (held manuscript sha256 b608db44…), Definition 9.7,
p.88 (extending Definition 2.8, p.18). -/
inductive TractType
  | A3 | A2 | B3 | B2 | C0 | C12 | C1s | C1z | C1g
  deriving DecidableEq

/-- The standing hypothesis of Definition 9.7: `F` is nondegenerate, symmetric, of arity `n ≥ 3`.
Cai–Ihm, Definition 9.7, p.88: "Let F be a nondegenerate, symmetric, artiy n ≥ 3 signature." -/
def TypeHyp (F : Sig 3) : Prop := 3 ≤ F.1 ∧ F.IsSymmetric ∧ ¬ F.IsDegenerate

/-- The number of coordinates of `x` equal to `c`. -/
def countVal {n : ℕ} (x : Fin n → Fin 3) (c : Fin 3) : ℕ :=
  (Finset.univ.filter fun t => x t = c).card

/-- The input `B^{n−1}G` (one `G`, in position 0). -/
def wBG (n : ℕ) : Fin n → Fin 3 := fun i => if i.val = 0 then 1 else 0

/-- The input `B^{n−2}R²` (`R` in positions 0 and 1). -/
def wBRR (n : ℕ) : Fin n → Fin 3 := fun i => if i.val < 2 then 2 else 0

/-- The condition of each of the first eight types at `T = I` (the **defining form**), applied
to a signature `H` (in use, `H = TF`). Cai–Ihm, Definition 9.7, p.88:
"1. 𝔄3: TF = a e1^{⊗n} + b e2^{⊗n} + c e3^{⊗n} for nonzero a, b, c ∈ C.
2. 𝔄2: TF = a e1^{⊗n} + b e2^{⊗n} for nonzero a, b ∈ C.
3. 𝔅3: TF = a β+^{⊗n} + b β−^{⊗n} + c e3^{⊗n} for nonzero a, b, c ∈ C.
4. 𝔅2: TF = a β+^{⊗n} + b β−^{⊗n} for nonzero a, b ∈ C.
5. ℭ0: TF with the condition that ⟨TF, β+⟩ = 0.
6. ℭ1_2: Y^{−1}TF = a e1^{⊗n} + λ Sym(e1, . . . , e1, e2) for nonzero λ ∈ C and any a ∈ C.
7. ℭ1_s: Y^{−1}TF = a e1^{⊗n} + λ Sym(e1, . . . , e1, e2) + d e3^{⊗n} for nonzero λ, d ∈ C and any
a ∈ C.
8. ℭ1_z: The support of Y^{−1}TF is a subset of B^n, B^{n−1}G, B^{n−1}R, B^{n−2}R^2 and their
permutations, Y^{−1}TF(B^{n−1}G) ≠ 0, and Y^{−1}TF(B^{n−2}R^2) ≠ 0."
For `ℭ¹_g` this records only `Y⁻¹TF ∈ 𝒞`; the exclusions are added in `DefForm`.

**Formalization Note.** `Y⁻¹TF` is `actT Yinv (TF)`; `⟨TF, β+⟩ = 0` is the vanishing of the
contraction with `β₊`. The supports in `ℭ¹_z` are by counts of `G` and `R`. -/
def DefForm₀ : TractType → Sig 3 → Prop
  | .A3, H => ∃ a b c : ℂ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
      H.2 = a • tpow e₁ H.1 + b • tpow e₂ H.1 + c • tpow e₃ H.1
  | .A2, H => ∃ a b : ℂ, a ≠ 0 ∧ b ≠ 0 ∧ H.2 = a • tpow e₁ H.1 + b • tpow e₂ H.1
  | .B3, H => ∃ a b c : ℂ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
      H.2 = a • tpow βp H.1 + b • tpow βm H.1 + c • tpow e₃ H.1
  | .B2, H => ∃ a b : ℂ, a ≠ 0 ∧ b ≠ 0 ∧ H.2 = a • tpow βp H.1 + b • tpow βm H.1
  | .C0, H => contractT H.2 βp = 0
  | .C12, H => ∃ a l : ℂ, l ≠ 0 ∧ actT Yinv H.2 = a • tpow e₁ H.1 + l • symUV e₁ e₂ H.1
  | .C1s, H => ∃ a l d : ℂ, l ≠ 0 ∧ d ≠ 0 ∧
      actT Yinv H.2 = a • tpow e₁ H.1 + l • symUV e₁ e₂ H.1 + d • tpow e₃ H.1
  | .C1z, H => (∀ x, actT Yinv H.2 x ≠ 0 →
        (countVal x 1 = 0 ∧ countVal x 2 ≤ 2) ∨ (countVal x 1 = 1 ∧ countVal x 2 = 0)) ∧
      actT Yinv H.2 (wBG H.1) ≠ 0 ∧ actT Yinv H.2 (wBRR H.1) ≠ 0
  | .C1g, H => InC ⟨H.1, actT Yinv H.2⟩

/-- `F` is of type `τ` in the sense of the first clause of `DefForm₀` (used to state the
exclusions of `ℭ¹_g`). -/
def IsType₀ (τ : TractType) (F : Sig 3) : Prop :=
  TypeHyp F ∧ ∃ T, IsOrth3 T ∧ DefForm₀ τ (act T F)

/-- The **defining form** of type `τ` for `H`: the condition of Definition 9.7 with `T = I`.
For `ℭ¹_g` it is `Y⁻¹H ∈ 𝒞` together with "not `ℭ⁰`, `ℭ¹₂`, `ℭ¹ₛ`, or `ℭ¹_z`". Cai–Ihm,
Definition 9.7, p.88: "9. ℭ1_g: Y^{−1}TF ∈ 𝒞 and F is not ℭ0, ℭ1_2, ℭ1_s, or ℭ1_z. … We say F is of
the defining form of the type if T can be chosen to be the identity matrix."

**Formalization Note.** The exclusions are stated for `H = TF`; being of a type is invariant under
orthogonal `T`, so this is the same as excluding the types for `F`. -/
def DefForm : TractType → Sig 3 → Prop
  | .C1g, H => InC ⟨H.1, actT Yinv H.2⟩ ∧ ¬ IsType₀ .C0 H ∧ ¬ IsType₀ .C12 H ∧
      ¬ IsType₀ .C1s H ∧ ¬ IsType₀ .C1z H
  | τ, H => DefForm₀ τ H

/-- `F` **is of type `τ`** (Definition 9.7): `F` is nondegenerate, symmetric, of arity `≥ 3`, and
some `T ∈ O(3, ℂ)` brings it to the defining form of `τ`. Cai–Ihm, Definition 9.7, p.88: "We say
F is one of the following types if there exists T ∈ O(3, C) that satisfies the given condition."
For arity 3, types 1–8 are those of Definition 2.8, p.18; Definition 9.7 states `ℭ¹_g`
implicitly, and this implicit form is used for every arity (Corollary 3.13 relates it to the
explicit ternary condition of Definition 2.8). -/
def IsType (τ : TractType) (F : Sig 3) : Prop :=
  TypeHyp F ∧ ∃ T, IsOrth3 T ∧ DefForm τ (act T F)

end Holant3Dich


