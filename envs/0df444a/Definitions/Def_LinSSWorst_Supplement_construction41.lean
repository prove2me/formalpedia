-- Prove2me | Definitions.Def_LinSSWorst_Supplement_construction41
-- name    : LinSSWorst_Supplement_construction41
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:46:31.960557+00:00
-- url     : https://prove2.me/theorems/f24b1ce4-4b07-4947-b475-d4bf4b5b840d
-- title:
--   The linear scheme of Construction 4.1 for a partitioned upslice (with Shamir sharing over an extension field, Definition A.4)
-- statement:
--   Let $F$ be a finite field, $[n]=L\sqcup R$ a partition with $|R|=q$, and $1\le t\le q$. A **trace** is a set $T\subseteq R$ with $|T|\ge t$; let $\mathcal T$ be the family of traces. For $U\subseteq L$ with $|U|=k-t$ and $T\in\mathcal T$, $\gamma_U(T)=1$ if $f_\Pi(U\cup T)=0$ and $0$ otherwise.
--
--   **Construction 4.1.** Let $s\in F$ be the secret. The dealer samples independent uniform $\eta\in F$ and $(\omega_T)_{T\in\mathcal T}$.
--   1. *Masking side.* For every $U\subseteq L$ with $|U|=k-t$, the value
--   $$m_U=s+\eta+\sum_{T\in\mathcal T}\gamma_U(T)\,\omega_T$$
--   is shared among the parties of $U$ by additive secret sharing with fresh randomness.
--   2. *Disclosure side.* (i) $\eta$ is shared among the parties of $R$ by the $F$-linear $t$-out-of-$q$ Shamir scheme of Definition A.4: over a degree-$m$ extension $K$ of $F$, with random $a_1,\dots,a_{t-1}\in K$, party $j$ receives $p(\alpha_j)$ for $p(X)=\eta+\sum_{i=1}^{t-1}a_iX^i$, written as $m$ coordinates over $F$; (ii) for every trace $T$, $\omega_T$ is given to each party of $R\setminus T$.
--
--   Every share is an $F$-linear combination of the secret and the dealer's randomness, so this is a linear map of (secret, randomness).
--
--   **Formalization Note** The map is an $F$-linear map from $F\times(\text{randomness}\to F)$ to the per-party share vectors, on finite index types (traces, masking sets, Shamir coordinates, additive-sharing randomness). The extension $K$ comes with an $F$-basis indexed by `Fin m`, and evaluation points `α : Fin n → K`; the conditions on them are hypotheses of Theorem 4.2. The last party of each additive sharing is the largest index of $U$. $\gamma_U(T)$ is the published `LinSSWorst.gamma`.
-- source:
--   Nir, Resolving the Worst-Case Complexity of Linear Secret Sharing, preprint (STOC 2027 submission, version of 2026-11-02, sha256 5521cfdb…), Construction 4.1, eqs. (4), (5), p.14; Definition A.4, pp.29–30; Definition A.5, p.30

import Mathlib
import Definitions.Def_LinSSWorst_construction31

namespace LinSSWorst.Supplement

variable {n : ℕ}

/-- The **traces** of §4, p.14, from O. Nir, *Resolving the Worst-Case Complexity of Linear Secret
Sharing*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 5521cfdb…): the sets `T ⊆ R` with
`|T| ≥ t`, where `R = Lᶜ` is the disclosure side. -/
abbrev Trace41 (L : Finset (Fin n)) (t : ℕ) := {T : Finset (Fin n) // T ⊆ Lᶜ ∧ t ≤ T.card}

/-- The masking sets of Construction 4.1, p.14: the sets `U ∈ (L choose k − t)`. -/
abbrev MaskSet41 (L : Finset (Fin n)) (k t : ℕ) := {U : Finset (Fin n) // U ⊆ L ∧ U.card = k - t}

/-- Index of the fresh additive-sharing randomness of Construction 4.1 (Masking side, item 1; Definition
A.5, p.30): one element `r_{U,j}` for every masking set `U` and every party `j ∈ U` other than the
designated last party of `U`, which is the largest index in `U`. -/
abbrev AddIdx41 (L : Finset (Fin n)) (k t : ℕ) :=
  {p : MaskSet41 L k t × Fin n // p.2 ∈ p.1.1 ∧ ∃ j ∈ p.1.1, p.2 < j}

/-- The dealer's randomness of Construction 4.1, p.14, as `F`-coordinates:
* `Sum.inl ()` is the pad `η ∈ F`;
* `Sum.inr (Sum.inl T)` is the trace pad `ω_T ∈ F`, for every trace `T`;
* `Sum.inr (Sum.inr (Sum.inl (i, c)))` is the `c`-th `F`-coordinate (in the chosen basis of `K` over `F`)
  of the Shamir coefficient `a_{i+1} ∈ K`, `i < t − 1` (Definition A.4);
* `Sum.inr (Sum.inr (Sum.inr p))` is the additive-sharing randomness `r_{U,j}` for `p = ((U, j), _)`. -/
abbrev RandIdx41 (L : Finset (Fin n)) (k t m : ℕ) :=
  Unit ⊕ Trace41 L t ⊕ (Fin (t - 1) × Fin m) ⊕ AddIdx41 L k t

/-- The share coordinates of party `i` in Construction 4.1, p.14:
* `Sum.inl U`, for every masking set `U ∋ i`: party `i`'s additive share of `m_U`;
* `Sum.inr (Sum.inl c)`, if `i ∈ R`, for `c < m`: the `c`-th `F`-coordinate of party `i`'s Shamir share of
  `η` (an element of `K`);
* `Sum.inr (Sum.inr T)`, if `i ∈ R`, for every trace `T` with `i ∉ T`: the pad `ω_T`. -/
abbrev ShareIdx41 (L : Finset (Fin n)) (k t m : ℕ) (i : Fin n) :=
  {U : MaskSet41 L k t // i ∈ U.1} ⊕ {_c : Fin m // i ∉ L} ⊕ {T : Trace41 L t // i ∉ L ∧ i ∉ T.1}

/-- The masked value `m_U = s + η + Σ_{T ∈ 𝒯} γ_U(T) ω_T` of (5), p.14, with `γ_U(T) = 1` iff
`f_Π(U ∪ T) = 0` ((4), p.14; the published `LinSSWorst.gamma`). -/
def mask41 (F : Type*) [Field F] (f : (Fin n → Bool) → Bool) (L : Finset (Fin n)) (k t m : ℕ)
    (U : MaskSet41 L k t) (s : F) (r : RandIdx41 L k t m → F) : F :=
  s + r (Sum.inl ()) + ∑ T : Trace41 L t, gamma F f U.1 T.1 * r (Sum.inr (Sum.inl T))

/-- Party `i`'s additive share of `m_U` (Construction 4.1, Masking side, item 1; Definition A.5):
`r_{U,i}` if `i` is not the largest index of `U`, and `m_U − Σ_j r_{U,j}` (the sum over the non-largest
`j ∈ U`) if it is. -/
def addShare41 (F : Type*) [Field F] (f : (Fin n → Bool) → Bool) (L : Finset (Fin n)) (k t m : ℕ)
    (U : MaskSet41 L k t) (i : Fin n) (s : F) (r : RandIdx41 L k t m → F) : F :=
  if h : i ∈ U.1 ∧ ∃ j ∈ U.1, i < j then r (Sum.inr (Sum.inr (Sum.inr ⟨(U, i), h⟩)))
  else mask41 F f L k t m U s r -
    ∑ p ∈ Finset.univ.filter (fun p : AddIdx41 L k t => p.1.1 = U),
      r (Sum.inr (Sum.inr (Sum.inr p)))

/-- The **Shamir share** `p(α_j) ∈ K` of party `j` (Definition A.4, pp.29–30), with
`p(X) = η + Σ_{i=1}^{t−1} a_i Xⁱ`, the secret `η ∈ F ⊆ K` and the random coefficients
`a_i = Σ_c r_{i,c} b_c ∈ K` given by their coordinates in the `F`-basis `b` of `K`. It is `F`-linear in
the dealer's randomness. -/
noncomputable def shamir41 (F : Type*) [Field F] {K : Type*} [Field K] [Algebra F K] (L : Finset (Fin n))
    (k t : ℕ) {m : ℕ} (b : Module.Basis (Fin m) F K) (α : Fin n → K) (j : Fin n) :
    (F × (RandIdx41 L k t m → F)) →ₗ[F] K where
  toFun p := algebraMap F K (p.2 (Sum.inl ())) +
    ∑ i : Fin (t - 1), (∑ c, p.2 (Sum.inr (Sum.inr (Sum.inl (i, c)))) • b c) * α j ^ (i.1 + 1)
  map_add' p p' := by
    simp only [Prod.snd_add, Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib, add_mul]
    ring
  map_smul' c p := by
    simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp only [Algebra.smul_def, map_mul, Finset.mul_sum, Finset.sum_mul, mul_add, mul_assoc]

/-- The shares of Construction 4.1, p.14, coordinate by coordinate. -/
noncomputable def shareVal41 (F : Type*) [Field F] {K : Type*} [Field K] [Algebra F K]
    (f : (Fin n → Bool) → Bool) (L : Finset (Fin n)) (k t : ℕ) {m : ℕ} (b : Module.Basis (Fin m) F K)
    (α : Fin n → K) (s : F) (r : RandIdx41 L k t m → F) (i : Fin n) : ShareIdx41 L k t m i → F
  | Sum.inl U => addShare41 F f L k t m U.1 i s r
  | Sum.inr (Sum.inl c) => b.coord c.1 (shamir41 F L k t b α i (s, r))
  | Sum.inr (Sum.inr T) => r (Sum.inr (Sum.inl T.1))

/-- **Construction 4.1** (Linear secret sharing for a partitioned upslice), p.14, for the partition
`[n] = L ⊔ R` with `R = Lᶜ`, `|R| = q`. With secret `s ∈ F`, the dealer samples independent uniform
`η` and `(ω_T)_{T ∈ 𝒯}` (`𝒯` the traces `T ⊆ R`, `|T| ≥ t`) and distributes:
* Masking side: for every `U ∈ (L choose k − t)`, `m_U = s + η + Σ_{T ∈ 𝒯} γ_U(T) ω_T` (5) is shared among
  the parties of `U` by additive secret sharing (with fresh randomness);
* Disclosure side: (1) `η` is shared among the parties of `R` by the `F`-linear `t`-out-of-`q` Shamir
  scheme of Definition A.4; (2) for every trace `T`, `ω_T` is given to each party in `R \ T`.

**Formalization Note.** The map is the `F`-linear map from `F × (RandIdx41 L k t m → F)` (secret and
random string) to the share vectors `(i : Fin n) → ShareIdx41 L k t m i → F`; numbering the finite index
types gives Definition A.3's `F^{1+ℓ_r} → F^{ℓ_1+⋯+ℓ_n}`. Definition A.4's Shamir scheme runs over a field
extension `K` of `F` with an `F`-basis `b : Basis (Fin m) F K` (so `K` has degree `m` over `F`) and
evaluation points `α j ∈ K` for the parties `j ∈ R`; each `K`-share is written as its `m` coordinates in
`b`, and the random coefficients `a_1, …, a_{t−1} ∈ K` are drawn uniformly by drawing their coordinates
uniformly. The requirements on `m`, `K` and `α` (degree `m = ⌈log_{|F|}(q + 1)⌉`, distinct nonzero
points) are hypotheses of Theorem 4.2. The designated last party of each additive sharing is the largest
index of `U`. `γ_U(T)` is the published `LinSSWorst.gamma`. -/
noncomputable def construction41 (F : Type*) [Field F] {K : Type*} [Field K] [Algebra F K]
    (f : (Fin n → Bool) → Bool) (L : Finset (Fin n)) (k t : ℕ) {m : ℕ} (b : Module.Basis (Fin m) F K)
    (α : Fin n → K) :
    (F × (RandIdx41 L k t m → F)) →ₗ[F] ((i : Fin n) → ShareIdx41 L k t m i → F) where
  toFun p := fun i => shareVal41 F f L k t b α p.1 p.2 i
  map_add' p p' := by
    funext i x
    rcases x with U | c | T
    · simp only [shareVal41, addShare41, Prod.fst_add, Prod.snd_add, Pi.add_apply]
      split_ifs <;>
        simp only [mask41, Prod.fst_add, Prod.snd_add, Pi.add_apply, Finset.sum_add_distrib,
          mul_add] <;> ring
    · simp only [shareVal41, Pi.add_apply]
      rw [show (p + p').1 = p.1 + p'.1 from rfl, show (p + p').2 = p.2 + p'.2 from rfl,
        ← Prod.mk_add_mk, map_add, map_add]
    · simp only [shareVal41, Prod.snd_add, Pi.add_apply]
  map_smul' c p := by
    funext i x
    rcases x with U | d | T
    · simp only [shareVal41, addShare41, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply]
      split_ifs <;>
        simp only [mask41, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
          Finset.mul_sum, mul_add, mul_sub, mul_left_comm c] <;> ring
    · simp only [shareVal41, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [show (c • p).1 = c • p.1 from rfl, show (c • p).2 = c • p.2 from rfl,
        ← Prod.smul_mk, map_smul, map_smul, smul_eq_mul]
    · simp only [shareVal41, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

end LinSSWorst.Supplement


