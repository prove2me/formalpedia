-- Prove2me | Definitions.Def_HoneycombCodes_Supplement_BnTypes
-- name    : HoneycombCodes_Supplement_BnTypes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:34:25.378846+00:00
-- url     : https://prove2.me/theorems/80555539-24cc-4f06-9a8b-7593b5663828
-- title:
--   The hyperoctahedral group $B_n$, its signed natural representation, and the irreducible types $S^\nu$ and $V_{\lambda,\mu}$
-- statement:
--   The **hyperoctahedral group** $B_n=C_2^n\rtimes S_n$ of signed permutations acts transitively on $X_n=\{\pm1\}^n$; the stabilizer of the all-ones word $o$ is the permutation subgroup $S_n$. The **natural signed representation** is $W=\mathbb C^n$ with $(\varepsilon,\pi)e_r=\varepsilon_{\pi(r)}e_{\pi(r)}$, and $\ell_o=n^{-1/2}(1,\dots,1)$ is the $S_n$-fixed unit vector.
--
--   A partition $\nu\vdash m$ is recorded by its weakly decreasing row lengths; $\nu'$ is its conjugate. An irreducible representation of $S_m$ **is of type $\nu$** (isomorphic to the Specht module $S^\nu$) when it admits nonzero intertwiners into both the permutation module $M^\nu=\mathrm{Ind}_{S_\nu}^{S_m}1$ (functions on tabloids of shape $\nu$) and the sign-twisted module $\mathrm{sgn}\otimes M^{\nu'}$; by a classical theorem $S^\nu$ is the unique irreducible common to both.
--
--   For a bipartition $(\lambda,\mu)$ with $|\lambda|+|\mu|=n$, an irreducible representation of $B_n$ **is of type $(\lambda,\mu)$** (isomorphic to $V_{\lambda,\mu}$) when it admits nonzero intertwiners into both $M^{\lambda,\mu}$ and $\mathrm{sgn}\otimes M^{\lambda',\mu'}$, where $M^{\lambda,\mu}$ is spanned by colored tabloids (each letter colored $0$ or $1$, with $\lambda_c$ letters of color $0$ and $\mu_c$ letters of color $1$ in row $c$), $S_n$ permutes letters and $\varepsilon\in C_2^n$ acts on a colored tabloid by the product of $\varepsilon_x$ over the letters $x$ of color $1$. With this convention the $\mu$-boxes carry the sign character of $C_2$, $W\cong V_{(n-1),(1)}$, and $\dim V_{\lambda,\mu}=\binom{n}{|\mu|}f^\lambda f^\mu$.
--
--   A **box transfer** moves one box between the two components: $(\lambda,\mu)\to(\lambda-\square_a,\mu+\square_b)$ (forward) or $(\lambda,\mu)\to(\lambda+\square_a,\mu-\square_b)$ (reverse).
--
--   These are the representation-theoretic objects of Sections 4 and 8: the ambient irreducibles $V_\omega$, the stabilizer types $E=S^\nu$ and the box-transfer graph.
--
--   **Formalization Note** $B_n$ is Mathlib's semidirect product $(\mathrm{Fin}\,n\to\mathbb Z^\times)\rtimes\mathrm{Perm}(\mathrm{Fin}\,n)$. The types are characterized intrinsically (by Clifford theory and the Young-symmetrizer characterization of $S^\nu$), so no explicit model of $S^\nu$ or $V_{\lambda,\mu}$ is fixed; intertwining is stated on the generators. The signed natural representation is a predicate fixing the representation on generators.
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), §4.1, pp.16–17 (PDF 18–19); §4.2, p.18 (PDF 20); §8, eqs. (93)–(96), p.40 (PDF 42)

import Mathlib

set_option autoImplicit false

namespace HoneycombCodes.Supplement

/-- The **hyperoctahedral group** `B_n = C₂ⁿ ⋊ S_n` of signed permutations, Gay, Granha Jeronimo,
Liu, *The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), §4.1,
p.16 (PDF 18).

**Formalization Note.** `C₂ = ℤˣ = {±1}`; a permutation `π` acts on sign vectors by
`(π • ε)(r) = ε(π⁻¹ r)` (Mathlib's `mulAutArrow`). The element `⟨ε, π⟩ = inl ε * inr π` sends a word
`x ∈ {±1}ⁿ` to `r ↦ ε(r) x(π⁻¹ r)`; the stabilizer of the all-ones word is the permutation subgroup
`inr (S_n)`. -/
abbrev Bn (n : ℕ) : Type := (Fin n → ℤˣ) ⋊[mulAutArrow] Equiv.Perm (Fin n)

/-- The **natural signed permutation representation** `W = ℂⁿ` of `B_n` (§4.1, p.16, PDF 18):
`⟨ε, π⟩ e_r = ε(π r) e_{π r}`, i.e. `inl ε` multiplies coordinate `s` by `ε(s)` and `inr π` permutes
coordinates, `(π · w)(s) = w(π⁻¹ s)`.

**Formalization Note.** A predicate on a representation on `EuclideanSpace ℂ (Fin n)`, fixing it on
the generators `inl ε`, `inr π` (which determine it); these formulas are compatible with the
semidirect-product law, so exactly one such representation exists. -/
def IsSignedNatural {n : ℕ} (ρW : Representation ℂ (Bn n) (EuclideanSpace ℂ (Fin n))) : Prop :=
  (∀ (ε : Fin n → ℤˣ) (w : EuclideanSpace ℂ (Fin n)),
      ρW (SemidirectProduct.inl ε) w = WithLp.toLp 2 (fun s => (((ε s : ℤˣ) : ℤ) : ℂ) * w s)) ∧
    ∀ (π : Equiv.Perm (Fin n)) (w : EuclideanSpace ℂ (Fin n)),
      ρW (SemidirectProduct.inr π) w = WithLp.toLp 2 (fun s => w (π⁻¹ s))

/-- The stabilizer-fixed unit vector `ℓ_o = n^{−1/2}(1, …, 1) ∈ W`, arXiv:2608.20287v2, §4.1, p.16,
and §4.3, p.18 (PDF 18, 20). -/
noncomputable def ellO (n : ℕ) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun _ => ((Real.sqrt n)⁻¹ : ℂ))

/-- A **partition** `p ⊢ m`, encoded by its row lengths `p 0 ≥ p 1 ≥ ⋯` (§4.1, p.17, PDF 19:
`f_θ = dim S^θ`, the empty partition allowed).

**Formalization Note.** `p : ℕ → ℕ` antitone with `p m = 0` and `Σ_{r < m} p r = m`; then
`p r = 0` for `r ≥ m`, and the number of rows is `#{r : p r > 0}`. -/
def IsPart (p : ℕ → ℕ) (m : ℕ) : Prop :=
  Antitone p ∧ p m = 0 ∧ ∑ r ∈ Finset.range m, p r = m

/-- The **conjugate partition** `p′(c) = #{r : p r > c}` of a partition of `m`. -/
def conjPart (p : ℕ → ℕ) (m : ℕ) : ℕ → ℕ :=
  fun c => ((Finset.range m).filter (fun r => c < p r)).card

/-- The two-row partition `(a, b)` (rows `a ≥ b`; meaningful when `b ≤ a`). -/
def twoRow (a b : ℕ) : ℕ → ℕ :=
  fun r => if r = 0 then a else if r = 1 then b else 0

/-- A **tabloid** of shape `p ⊢ m`: an assignment `t : [m] → rows` with exactly `p c` letters in
row `c`; tabloids index the basis of the permutation module `M^p = Ind_{S_p}^{S_m} 1`. -/
def IsTabloid {m : ℕ} (p : ℕ → ℕ) (t : Fin m → Fin m) : Prop :=
  ∀ c : Fin m, (Finset.univ.filter (fun x => t x = c)).card = p c

/-- `ρ` is an irreducible `S_m`-representation **isomorphic to the Specht module `S^p`**, §4.1,
p.17 (PDF 19), for a partition `p ⊢ m`.

**Formalization Note.** Characterized by the classical fact that `S^p` is the unique irreducible
constituent common to the permutation module `M^p = Ind_{S_p} 1` and the sign-twisted module
`sgn ⊗ M^{p′}` (`p′` the conjugate), e.g. Fulton–Harris, *Representation Theory*, §4.1. Both modules
are realized as the functions on all maps `[m] → [m]` that vanish off the tabloids of the shape,
with `(π · F)(t) = F(t ∘ π)`, resp. `sgn(π) F(t ∘ π)`; the condition is a nonzero intertwiner into
each. This is independent of any model of `S^p` (Sagan's polytabloid model satisfies it). -/
def IsSpechtType {m : ℕ} {A : Type*} [AddCommGroup A] [Module ℂ A]
    (ρ : Representation ℂ (Equiv.Perm (Fin m)) A) (p : ℕ → ℕ) : Prop :=
  IsPart p m ∧ ρ.IsIrreducible ∧
    (∃ f : A →ₗ[ℂ] ((Fin m → Fin m) → ℂ), f ≠ 0 ∧
      (∀ (a : A) (t : Fin m → Fin m), ¬ IsTabloid p t → f a t = 0) ∧
      ∀ (π : Equiv.Perm (Fin m)) (a : A), f (ρ π a) = fun t => f a (t ∘ π)) ∧
    (∃ f : A →ₗ[ℂ] ((Fin m → Fin m) → ℂ), f ≠ 0 ∧
      (∀ (a : A) (t : Fin m → Fin m), ¬ IsTabloid (conjPart p m) t → f a t = 0) ∧
      ∀ (π : Equiv.Perm (Fin m)) (a : A),
        f (ρ π a) = fun t => (((Equiv.Perm.sign π : ℤˣ) : ℤ) : ℂ) * f a (t ∘ π))

/-- A **colored tabloid** of bishape `(λ, µ)` on `[n]`: `t : [n] → {0, 1} × rows` with exactly
`λ c` letters of color `0` in row `c` and `µ c` letters of color `1` in row `c`. They index the
basis of `M^{λ,µ} = Ind_{C₂ⁿ ⋊ (S_λ × S_µ)}^{B_n} χ`, where `χ(ε) = Π_{color 1} ε`. -/
def IsColoredTabloid {n : ℕ} (lam mu : ℕ → ℕ) (t : Fin n → Fin 2 × Fin n) : Prop :=
  ∀ c : Fin n, (Finset.univ.filter (fun x => t x = (0, c))).card = lam c ∧
    (Finset.univ.filter (fun x => t x = (1, c))).card = mu c

/-- The sign character `χ_t(ε) = Π_{x : color(t x) = 1} ε(x)` of a colored tabloid. -/
def colorChar {n : ℕ} (t : Fin n → Fin 2 × Fin n) (ε : Fin n → ℤˣ) : ℂ :=
  ∏ x ∈ Finset.univ.filter (fun x => (t x).1 = 1), (((ε x : ℤˣ) : ℤ) : ℂ)

/-- `ρ` is an irreducible `B_n`-representation **isomorphic to `V_{λ,µ}`**, the irreducible of
bipartition `(λ, µ)`, `|λ| + |µ| = n`, §4.1, p.17 (PDF 19), with the convention fixed by
`W ≅ V_{(n−1),(1)}` (§4.2, p.18): the `µ`-boxes carry the sign character of `C₂`, so
`Res_{C₂ⁿ} V_{λ,µ}` consists of the characters with exactly `|µ|` minus signs and
`dim V_{λ,µ} = C(n, |µ|) f_λ f_µ`.

**Formalization Note.** By Clifford theory `V_{λ,µ}` is the unique irreducible constituent common to
`M^{λ,µ}` (colored tabloids of bishape `(λ, µ)`, `inl ε` acting by `χ_t(ε)`, `inr π` by
`F ↦ F(· ∘ π)`) and `sgn ⊗ M^{λ′,µ′}` (conjugate shapes, `inr π` acting with the extra factor
`sgn π`), exactly as for `IsSpechtType`; the condition is a nonzero `B_n`-intertwiner into each,
stated on the generators `inl ε`, `inr π`. -/
def IsBnType {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Bn n) V) (lam mu : ℕ → ℕ) : Prop :=
  ∃ i : ℕ, i ≤ n ∧ IsPart lam (n - i) ∧ IsPart mu i ∧ ρ.IsIrreducible ∧
    (∃ f : V →ₗ[ℂ] ((Fin n → Fin 2 × Fin n) → ℂ), f ≠ 0 ∧
      (∀ (v : V) (t : Fin n → Fin 2 × Fin n), ¬ IsColoredTabloid lam mu t → f v t = 0) ∧
      (∀ (ε : Fin n → ℤˣ) (v : V),
        f (ρ (SemidirectProduct.inl ε) v) = fun t => colorChar t ε * f v t) ∧
      ∀ (π : Equiv.Perm (Fin n)) (v : V),
        f (ρ (SemidirectProduct.inr π) v) = fun t => f v (t ∘ π)) ∧
    (∃ f : V →ₗ[ℂ] ((Fin n → Fin 2 × Fin n) → ℂ), f ≠ 0 ∧
      (∀ (v : V) (t : Fin n → Fin 2 × Fin n),
        ¬ IsColoredTabloid (conjPart lam (n - i)) (conjPart mu i) t → f v t = 0) ∧
      (∀ (ε : Fin n → ℤˣ) (v : V),
        f (ρ (SemidirectProduct.inl ε) v) = fun t => colorChar t ε * f v t) ∧
      ∀ (π : Equiv.Perm (Fin n)) (v : V),
        f (ρ (SemidirectProduct.inr π) v) =
          fun t => (((Equiv.Perm.sign π : ℤˣ) : ℤ) : ℂ) * f v (t ∘ π))

/-- A **box transfer** between bipartitions (§4.2, p.18, and eq. (96), p.40, PDF 20, 42): either
a forward edge `(λ, µ) → (λ − □_a, µ + □_b)` (one box removed from row `a` of `λ`, one added to row
`b` of `µ`) or a reverse edge `(λ, µ) → (λ + □_a, µ − □_b)`. -/
def IsBoxTransfer (src tgt : (ℕ → ℕ) × (ℕ → ℕ)) : Prop :=
  (∃ a b : ℕ, 1 ≤ src.1 a ∧ tgt.1 = Function.update src.1 a (src.1 a - 1) ∧
      tgt.2 = Function.update src.2 b (src.2 b + 1)) ∨
    ∃ a b : ℕ, 1 ≤ src.2 b ∧ tgt.1 = Function.update src.1 a (src.1 a + 1) ∧
      tgt.2 = Function.update src.2 b (src.2 b - 1)

end HoneycombCodes.Supplement


