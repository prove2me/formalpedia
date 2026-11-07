-- Prove2me | Definitions.Def_LinSSWorst_construction31
-- name    : LinSSWorst_construction31
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:05:00.431212+00:00
-- url     : https://prove2.me/theorems/ebc37857-6bc5-4a44-a145-35883490f7a3
-- title:
--   The coefficient $\gamma_U(T)$ (2) and the linear scheme of Construction 3.1
-- statement:
--   Let $F$ be a finite field, $f$ a function on $\{0,1\}^n$, and $[n]=L\sqcup R$ a partition of the parties, with $R=[n]\setminus L$. For $U\subseteq L$ and $T\subseteq R$ define the public coefficient
--   $$\gamma_U(T)=\begin{cases}1 & \text{if } f(U\cup T)=0,\\ 0 & \text{otherwise.}\end{cases}$$
--
--   **Construction 3.1.** Let $s\in F$ be the secret. The dealer samples independent uniform pads $(\omega_T)_{T\subseteq R}$ and, for every $U\subseteq L$, computes
--   $$m_U=s+\sum_{T\subseteq R}\gamma_U(T)\,\omega_T .$$
--   1. *Masking side.* For every nonempty $U\subseteq L$, $m_U$ is shared among the parties of $U$ by additive secret sharing, each $U$ with its own fresh randomness.
--   2. *Disclosure side.* Every party of $R$ receives a copy of $m_\emptyset$, and for every $T\subseteq R$ the pad $\omega_T$ is given to each party in $R\setminus T$.
--
--   All shares are $F$-linear combinations of the secret and the dealer's random elements, so the construction is a linear map of (secret, randomness).
--
--   **Formalization Note** Subsets of parties are `Finset (Fin n)` and `f(U ∪ T)` is `f` at the indicator of `U ∪ T`. The dealer's randomness is indexed by `RandIdx L`: one pad per `T ⊆ Lᶜ`, and one element $r_{U,j}$ for every `U ⊆ L` and every `j ∈ U` other than the largest index of `U`, which is the designated last party of the additive sharing of $m_U$. Party `i`'s coordinates are `ShareIdx L i`: one per `U ⊆ L` containing `i`, and, when `i ∉ L`, one for $m_\emptyset$ and one per `T ⊆ Lᶜ` not containing `i`. The map is defined for every `L`; Theorem 3.2 assumes `L` and `Lᶜ` nonempty.
-- source:
--   Nir, Resolving the Worst-Case Complexity of Linear Secret Sharing, preprint (STOC 2027 submission, version of 2026-11-02, sha256 5521cfdb…), §3, eq. (2), p.11; Construction 3.1, eq. (3), p.12

import Mathlib

namespace LinSSWorst

variable {n : ℕ}

/-- The **public coefficient** `γ_U(T)` of (2), p.11, from O. Nir, *Resolving the Worst-Case
Complexity of Linear Secret Sharing*, preprint (STOC 2027 submission, version of 2026-11-02,
sha256 5521cfdb…): `γ_U(T) = 1` if `f(U ∪ T) = 0` (the coalition `U ∪ T` is unauthorized), and
`γ_U(T) = 0` otherwise.

**Formalization Note.** A set of parties `U ∪ T ⊆ [n]` is passed to `f` as its indicator string
`j ↦ decide (j ∈ U ∪ T)`. -/
def gamma (F : Type*) [Field F] (f : (Fin n → Bool) → Bool) (U T : Finset (Fin n)) : F :=
  if f (fun j => decide (j ∈ U ∪ T)) = false then 1 else 0

/-- Index of the pads `(ω_T)_{T ⊆ R}` of Construction 3.1, p.12, where `R = Lᶜ` is the
disclosure side. -/
abbrev PadIdx (L : Finset (Fin n)) := {T : Finset (Fin n) // T ⊆ Lᶜ}

/-- Index of the fresh additive-sharing randomness of Construction 3.1, p.12: one element
`r_{U,j}` for every nonempty `U ⊆ L` and every party `j ∈ U` other than the designated last party
of `U`, which is the largest index in `U` (Definition A.5, p.30, run on `U` with its own fresh
randomness). -/
abbrev AddIdx (L : Finset (Fin n)) :=
  {p : Finset (Fin n) × Fin n // p.1 ⊆ L ∧ p.2 ∈ p.1 ∧ ∃ k ∈ p.1, p.2 < k}

/-- The dealer's randomness of Construction 3.1: the pads and the additive-sharing randomness,
all independent and uniform when the random string is drawn uniformly. -/
abbrev RandIdx (L : Finset (Fin n)) := PadIdx L ⊕ AddIdx L

/-- The share coordinates of party `i` in Construction 3.1, p.12: one coordinate for every
`U ⊆ L` with `i ∈ U` (party `i`'s additive share of `m_U`), and, if `i ∉ L` (so `i ∈ R`), one
coordinate `none` for the copy of `m_∅` and one coordinate `some T` for every `T ⊆ R` with
`i ∉ T` (the pad `ω_T`). -/
abbrev ShareIdx (L : Finset (Fin n)) (i : Fin n) :=
  {U : Finset (Fin n) // U ⊆ L ∧ i ∈ U} ⊕
    {_o : Option {T : Finset (Fin n) // T ⊆ Lᶜ ∧ i ∉ T} // i ∉ L}

/-- The masked value `m_U = s + Σ_{T ⊆ R} γ_U(T) ω_T` of (3), p.12, as a function of the secret
`s` and the dealer's random string `r` (`ω_T = r (inl T)`). -/
def mask (F : Type*) [Field F] (f : (Fin n → Bool) → Bool) (L U : Finset (Fin n)) (s : F)
    (r : RandIdx L → F) : F :=
  s + ∑ T : PadIdx L, gamma F f U T.1 * r (Sum.inl T)

/-- Party `i`'s additive share of `m_U` (Construction 3.1, Masking side, item 1; Definition A.5):
`r_{U,i}` if `i` is not the largest index of `U`, and `m_U − Σ_{j} r_{U,j}` (the sum over the
non-largest `j ∈ U`) if it is. -/
def addShare (F : Type*) [Field F] (f : (Fin n → Bool) → Bool) (L U : Finset (Fin n)) (i : Fin n)
    (s : F) (r : RandIdx L → F) : F :=
  if h : U ⊆ L ∧ i ∈ U ∧ ∃ k ∈ U, i < k then r (Sum.inr ⟨(U, i), h⟩)
  else mask F f L U s r - ∑ p ∈ Finset.univ.filter (fun p : AddIdx L => p.1.1 = U), r (Sum.inr p)

/-- The shares of Construction 3.1, p.12, coordinate by coordinate. -/
def shareVal (F : Type*) [Field F] (f : (Fin n → Bool) → Bool) (L : Finset (Fin n)) (s : F)
    (r : RandIdx L → F) (i : Fin n) : ShareIdx L i → F
  | Sum.inl U => addShare F f L U.1 i s r
  | Sum.inr ⟨none, _⟩ => mask F f L ∅ s r
  | Sum.inr ⟨some T, _⟩ => r (Sum.inl ⟨T.1, T.2.1⟩)

/-- **Construction 3.1** (Linear scheme for general access structures), p.12, for the partition
`[n] = L ⊔ R` with `R = Lᶜ`. With secret `s` and uniform independent pads `(ω_T)_{T ⊆ R}`:
* Masking side: for every nonempty `U ⊆ L`, `m_U = s + Σ_{T ⊆ R} γ_U(T) ω_T` is shared among the
  parties of `U` by additive secret sharing with fresh randomness;
* Disclosure side: every party of `R` gets a copy of `m_∅`, and for every `T ⊆ R` the pad `ω_T`
  goes to each party of `R \ T`.

**Formalization Note.** The map is the `F`-linear map from `F × (RandIdx L → F)` (secret and
random string) to the share vectors `(i : Fin n) → ShareIdx L i → F`. `RandIdx L` and `ShareIdx L i`
are finite types; `F^{1+ℓ_r}` and `F^{ℓ_1+⋯+ℓ_n}` of Definition A.3 are obtained by numbering
them. The designated last party of each additive sharing of `m_U` is the largest index in `U`.
Nonemptiness of `L` and `R` is not needed to define the map; Theorem 3.2 assumes it. -/
def construction31 (F : Type*) [Field F] (f : (Fin n → Bool) → Bool) (L : Finset (Fin n)) :
    (F × (RandIdx L → F)) →ₗ[F] ((i : Fin n) → ShareIdx L i → F) where
  toFun p := fun i => shareVal F f L p.1 p.2 i
  map_add' p p' := by
    funext i k
    rcases k with U | ⟨_ | T, h⟩ <;>
      simp only [shareVal, addShare, Prod.fst_add, Prod.snd_add, Pi.add_apply] <;>
      (try split_ifs) <;>
      simp only [mask, Prod.fst_add, Prod.snd_add, Pi.add_apply, Finset.sum_add_distrib,
        mul_add] <;> ring
  map_smul' c p := by
    funext i k
    rcases k with U | ⟨_ | T, h⟩ <;>
      simp only [shareVal, addShare, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply] <;>
      (try split_ifs) <;>
      simp only [mask, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum, mul_add, mul_sub, mul_left_comm c] <;> ring

end LinSSWorst


