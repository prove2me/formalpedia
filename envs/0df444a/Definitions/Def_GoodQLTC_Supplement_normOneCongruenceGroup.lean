-- Prove2me | Definitions.Def_GoodQLTC_Supplement_normOneCongruenceGroup
-- name    : GoodQLTC_Supplement_normOneCongruenceGroup
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:59:47.537199+00:00
-- url     : https://prove2.me/theorems/f030d637-57a2-4b0d-b002-2805fe4bdd29
-- title:
--   Quaternion algebras, totally definite, reduced norm one, maximal orders, norm-one congruence groups
-- statement:
--   Let $K$ be a number field with ring of integers $\mathcal O_K$; for a finite place $v$ write $K_v$, $\mathcal O_v$ for the completion and its valuation ring.
--
--   1. A **quaternion algebra** over $K$ is a central simple $K$-algebra $B$ of dimension four.
--   2. $B$ is **totally definite** if $K$ is totally real and $B\otimes_{K,\sigma}\mathbb R\cong\mathbb H$ (as $\mathbb R$-algebras) for every real embedding $\sigma$.
--   3. $x\in B$ has **reduced norm one** if $\mathrm{nrd}(x)=x\bar x=1$; equivalently $\det\psi(1\otimes x)=1$ for every field extension $E/K$ and every splitting $\psi:E\otimes_K B\cong M_2(E)$.
--   4. An **order** is an $\mathcal O_K$-subalgebra $M\subseteq B$ containing $1$, finitely generated as an $\mathcal O_K$-module and spanning $B$ over $K$; it is **maximal** if no larger order contains it. Its completion is $M_v:=M\otimes_{\mathcal O_K}\mathcal O_v$, the $\mathcal O_v$-span of $1\otimes M$ in $B_v:=K_v\otimes_K B$.
--   5. For distinct finite places $S=\{v_1,\dots,v_t\}$ and a nonzero ideal $\mathfrak n\subseteq\mathcal O_K$, the **norm-one congruence group** of level $\mathfrak n$ is
--   $$\Gamma(\mathfrak n):=\{x\in B:\ \mathrm{nrd}(x)=1,\ x_v\in M_v\ \text{for every finite } v\notin S,\ x_v-1\in\mathfrak n M_v\ \text{for every finite } v\mid\mathfrak n\}.$$
--   6. Given splittings $\varphi_i:B_{v_i}\cong M_2(K_{v_i})$, an element $x\in B^\times$ acts on the $i$-th tree $T(K_{v_i})$ through $\varphi_i(1\otimes x)\in\mathrm{GL}_2(K_{v_i})$.
--
--   The paper's groups (11.1) are $\Gamma(3^\nu\mathcal O_K)$ with $3\mathcal O_K$ prime; these definitions are the arithmetic layer of Theorem 11.1.
--
--   **Formalization Note** The reduced norm is expressed through splittings (for a quaternion algebra $\det\psi(1\otimes x)=\mathrm{nrd}(x)$ for every splitting, and splittings exist), because Mathlib's `Algebra.norm` is $\mathrm{nrd}^2$. An $\mathcal O_K$-subalgebra is a subring stable under multiplication by $\mathcal O_K$; finite generation is written with an explicit finite generating set. $\mathfrak n M_v$ is the $\mathcal O_v$-span of $1\otimes am$, $a\in\mathfrak n$, $m\in M$; $v\mid\mathfrak n$ is $\mathfrak n\subseteq v$.
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), §11.2, p.36 (PDF 39): quaternion algebra, split, totally definite, nrd, (maximal) order, M_v, H(R); Equation (11.1), p.36

import Mathlib

namespace GoodQLTC.Supplement

open NumberField TensorProduct IsDedekindDomain Quaternion

/-- A **quaternion algebra** over `K`, Gay–Jeronimo, arXiv:2609.20780 (held version), §11.2, p.36:
a central simple `K`-algebra of dimension four. -/
def IsQuaternionAlgebra (K : Type) [Field K] (B : Type) [Ring B] [Algebra K B] : Prop :=
  Algebra.IsCentral K B ∧ IsSimpleRing B ∧ Module.finrank K B = 4

/-- A **totally definite** quaternion algebra, Gay–Jeronimo, arXiv:2609.20780 (held version), §11.2,
p.36: `K` is totally real and `B ⊗_{K,σ} ℝ ≅ ℍ` at every real embedding `σ`.

**Formalization Note.** `ℝ` is a `K`-algebra through `σ`; `ℍ` is Mathlib's Hamilton quaternions
`ℍ[ℝ]`; the isomorphism is of `ℝ`-algebras. -/
def IsTotallyDefinite (K : Type) [Field K] [NumberField K] (B : Type) [Ring B] [Algebra K B] :
    Prop :=
  IsTotallyReal K ∧
    ∀ σ : K →+* ℝ, letI := σ.toAlgebra; Nonempty (ℝ ⊗[K] B ≃ₐ[ℝ] ℍ[ℝ])

/-- `x` has **reduced norm one**, `nrd(x) = x x̄ = 1`, Gay–Jeronimo, arXiv:2609.20780 (held version),
§11.2, p.36, for an element of a quaternion algebra `A` over a field `F`.

**Formalization Note.** The reduced norm is computed through splittings: for every field extension
`E/F` and every `E`-algebra isomorphism `ψ : E ⊗_F A ≅ M₂(E)`, `det ψ(1 ⊗ x) = 1`. For a quaternion
algebra `det ψ(1 ⊗ x) = nrd(x)` for every splitting `ψ`, and splittings exist (over an algebraic
closure, and in the theorems at the split places `v_i`), so this is exactly `nrd(x) = 1`. Mathlib's
`Algebra.norm` would be `nrd(x)²` and is not used. -/
def IsReducedNormOne {F : Type} [Field F] {A : Type} [Ring A] [Algebra F A] (x : A) : Prop :=
  ∀ (E : Type) [Field E] [Algebra F E] (ψ : E ⊗[F] A ≃ₐ[E] Matrix (Fin 2) (Fin 2) E),
    (ψ (1 ⊗ₜ x)).det = 1

/-- An **order** of a quaternion algebra `B/K`, Gay–Jeronimo, arXiv:2609.20780 (held version), §11.2,
p.36: an `O_K`-subalgebra containing `1`, finitely generated as an `O_K`-module and spanning `B`
over `K`.

**Formalization Note.** An `O_K`-subalgebra is a subring `M` of `B` (so `1 ∈ M`) stable under
multiplication by `O_K ⊆ K`; "finitely generated" is: there is a finite `S ⊆ M` with
`M = ∑_{s∈S} O_K s`. -/
def IsOrder (K : Type) [Field K] [NumberField K] {B : Type} [Ring B] [Algebra K B]
    (M : Subring B) : Prop :=
  (∀ a : 𝓞 K, ∀ m ∈ M, algebraMap K B (a : K) * m ∈ M) ∧
  (∃ S : Finset B, (S : Set B) ⊆ M ∧
    ∀ m ∈ M, ∃ c : B → 𝓞 K, m = ∑ s ∈ S, algebraMap K B (c s : K) * s) ∧
  Submodule.span K (M : Set B) = ⊤

/-- A **maximal order**, Gay–Jeronimo, arXiv:2609.20780 (held version), §11.2, p.36: an order that is
contained in no larger order. -/
def IsMaximalOrder (K : Type) [Field K] [NumberField K] {B : Type} [Ring B] [Algebra K B]
    (M : Subring B) : Prop :=
  IsOrder K M ∧ ∀ M' : Subring B, IsOrder K M' → M ≤ M' → M' = M

/-- The `O_v`-span of `{1 ⊗ s : s ∈ S}` inside `B_v := K_v ⊗_K B`, for a finite place `v` of `K`
(arXiv:2609.20780, §11.2–11.3, pp.36: `M_v := M ⊗_{O_K} O_v` is `localSpan v M`, and
`𝔫 M_v` is `localSpan v (𝔫 M)`). -/
def localSpan {K : Type} [Field K] [NumberField K] {B : Type} [Ring B] [Algebra K B]
    (v : HeightOneSpectrum (𝓞 K)) (S : Set B) : Set (v.adicCompletion K ⊗[K] B) :=
  {y | ∃ (n : ℕ) (c : Fin n → v.adicCompletionIntegers K) (s : Fin n → B),
    (∀ j, s j ∈ S) ∧ y = ∑ j, ((c j : v.adicCompletion K) ⊗ₜ s j)}

/-- The products `𝔫 M := {a m : a ∈ 𝔫, m ∈ M}` of an ideal of `O_K` and a subring of `B`. -/
def idealMul {K : Type} [Field K] [NumberField K] {B : Type} [Ring B] [Algebra K B]
    (𝔫 : Ideal (𝓞 K)) (M : Subring B) : Set B :=
  {b | ∃ a ∈ 𝔫, ∃ m ∈ M, b = algebraMap K B (a : K) * m}

/-- The **norm-one congruence group** of level `𝔫` away from `S = {v_1, …, v_t}`, Gay–Jeronimo,
arXiv:2609.20780 (held version), Equation (11.1), p.36, in the reading recorded for Theorem 11.1:
`Γ(𝔫) := {x ∈ B : nrd x = 1, x_v ∈ M_v for every finite v ∉ S, x_v − 1 ∈ 𝔫 M_v for every finite
v ∣ 𝔫}`.

**Formalization Note.** Elements are units of `B` (`nrd x = 1` makes `x` a unit); `x_v = 1 ⊗ x`;
`v ∣ 𝔫` is `𝔫 ≤ v`. The paper's groups (11.1) are `𝔫 = 3^ν O_K` (with `3O_K` prime). -/
def normOneCongruenceGroup {K : Type} [Field K] [NumberField K] {B : Type} [Ring B] [Algebra K B]
    (M : Subring B) {t : ℕ} (v : Fin t → HeightOneSpectrum (𝓞 K)) (𝔫 : Ideal (𝓞 K)) : Set Bˣ :=
  {x | IsReducedNormOne (F := K) (x : B) ∧
    (∀ w : HeightOneSpectrum (𝓞 K), w ∉ Set.range v → (1 : w.adicCompletion K) ⊗ₜ (x : B) ∈ localSpan w M) ∧
    (∀ w : HeightOneSpectrum (𝓞 K), 𝔫 ≤ w.asIdeal →
      (1 : w.adicCompletion K) ⊗ₜ ((x : B) - 1) ∈ localSpan w (idealMul 𝔫 M))}

/-- The action of `x ∈ B^×` on the `i`-th tree through the splitting `φ_i : B_{v_i} ≅ M₂(K_{v_i})`:
`x ↦ φ_i(1 ⊗ x) ∈ GL₂(K_{v_i})` (arXiv:2609.20780, §11.2, p.36). -/
noncomputable def splitAct {K : Type} [Field K] [NumberField K] {B : Type} [Ring B] [Algebra K B]
    {t : ℕ} {v : Fin t → HeightOneSpectrum (𝓞 K)}
    (φ : ∀ i, (v i).adicCompletion K ⊗[K] B ≃ₐ[(v i).adicCompletion K]
      Matrix (Fin 2) (Fin 2) ((v i).adicCompletion K))
    (x : Bˣ) : ∀ i, GL (Fin 2) ((v i).adicCompletion K) :=
  fun i => Units.map ((φ i).toRingEquiv.toMonoidHom.comp
    (Algebra.TensorProduct.includeRight (R := K) (A := (v i).adicCompletion K) (B := B)).toMonoidHom) x

end GoodQLTC.Supplement


