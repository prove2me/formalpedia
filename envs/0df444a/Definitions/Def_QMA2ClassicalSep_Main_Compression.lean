-- Prove2me | Definitions.Def_QMA2ClassicalSep_Main_Compression
-- name    : QMA2ClassicalSep_Main_Compression
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:04:21.919704+00:00
-- url     : https://prove2.me/theorems/6dceec84-a328-4ead-b379-2d328206ded3
-- title:
--   The compression isometries $J_X$ (Carolan–Majenz) and $J_\pm$
-- statement:
--   For a finite set $X$ and a partial bijection $f$ on $X$ with $|f|=r$, the **completion state** is $|T_f\rangle=((|X|-r)!)^{-1/2}\sum_{\varphi\in\mathrm{Sym}(X),\ \varphi|_{\mathrm{dom} f}=f}|\varphi\rangle$, and $E_r|f\rangle=|T_f\rangle$. Let $\mathcal H_{\le r}=\operatorname{span}\{|T_f\rangle:|f|\le r\}$, $\Pi_r$ the projector onto $\mathcal H_{\le r}\ominus\mathcal H_{\le r-1}$, $\Gamma_r=\Pi_rE_r$ and $G_r=\Gamma_r\Gamma_r^\dagger$. The compression isometry of [CM26, Theorem 4.2] is
--   $$
--   J_X=\widetilde V=\bigoplus_{r}\widetilde V_r,\qquad \widetilde V_r=\Gamma_r^\dagger G_r^{-1/2}.
--   $$
--   On oracle parameters,
--   $$
--   J_+|(\pi_p),h_A,h_B\rangle=\Big(\bigotimes_{p}J_V|\pi_p\rangle\Big)\otimes2^{-M/2}\sum_{S\subseteq\mathcal X}h(S)|S\rangle,\qquad
--   J_-|(\pi_p),h_A,h_B,\theta\rangle=|\theta\rangle\otimes\Big(\bigotimes_p\bigotimes_{\mathcal B\ne\emptyset}J_{\mathcal B}|\pi_p|_{\mathcal B}\rangle\Big)\otimes2^{-M/2}\sum_Sh(S)|S\rangle,
--   $$
--   with $M=|\mathcal X|$ and $h(S)=\prod_{u\in S}h(u)$. Also $\Pi_\pm=J_\pm J_\pm^\dagger$ and $Q_{\pm,a}=(I-P_{\pm,a})\mathrm{Dec}_{\pm,a}P_{\pm,a}$.
--
--   These maps carry a superposition of oracle parameters to a superposition of small records; they are the representation in which the query lower bound is proved.
--
--   **Formalization Note** $J_X$ is taken from J. Carolan and C. Majenz, *Compressed Permutation Oracles Revisited*, arXiv:2609.28469v1, §4.1 and Remark 4.4 ("compression isometry" means $\widetilde V$). $G_r^{-1/2}$ and the projectors are computed with the Hermitian functional calculus (inverse on the range, zero on the kernel). A set $X$ inside $V$ is handled as the permutations of $V$ fixing every point outside $X$.
-- source:
--   Sabee Grewal, Saachi Mutreja, Kabir Tomer, A classical oracle separation between QMA and QMA(2), STOC 2027 submission #618 (October 2026), SHA-256 79883d9d08b98b41b1bb600a6644f3f578ecb803702383a9f2a58d5bc7dacedf, Section 6.1, pp. 25–26 (J_X of [CM26, Theorem 4.2], J_+, J_-); Prop. 6.13, p. 49 (Π_τ, Q_{τ,a}); J_X from Carolan–Majenz, arXiv:2609.28469v1, §4.1

import Definitions.Def_QMA2ClassicalSep_Main_Records

set_option autoImplicit false

/-!
# The compression isometries `J_X` (Carolan–Majenz) and `J₊`, `J₋`

Grewal, Mutreja, Tomer, *A classical oracle separation between QMA and QMA(2)*, STOC 2027
submission #618, Section 6.1, pp. 25–26: "let `J_X` be the compression isometry of
[CM26, Theorem 4.2]", and the definitions of `J₊`, `J₋`.

`J_X` is the isometry `Ṽ` of J. Carolan and C. Majenz, *Compressed Permutation Oracles
Revisited*, arXiv:2609.28469v1 (23 Sep 2026), Section 4.1 (Remark 4.4: "the phrase compression
isometry refers to `Ṽ`"). For a finite set `X` (of size `N` there):
* completion states `|T_f⟩ = ((N − r)!)^{-1/2} Σ_{φ ∈ Sym(X), φ|_{dom f} = f} |φ⟩` for a partial
  bijection `f` with `|f| = r`; synthesis `E_r |f⟩ = |T_f⟩`;
* `ℋ_{≤r} = span{|T_f⟩ : |f| ≤ r}`, `Π_r` the projector onto `ℋ_r = ℋ_{≤r} ⊖ ℋ_{≤r−1}`;
* `Γ_r = Π_r E_r`, `G_r = Γ_r Γ_r†`, `Ṽ_r = Γ_r† G_r^{-1/2}` (on `ℋ_r`), `Ṽ = ⊕_r Ṽ_r`.
Here `X` is a finite set `B` inside an ambient type `α`; permutations of `B` are the permutations
of `α` that fix every point outside `B`.
-/

namespace QMA2ClassicalSep.Main

open Matrix

attribute [local instance] Classical.propDecidable

section CM

variable (α : Type) [Fintype α] [DecidableEq α] (B : Finset α)

/-- `Sym(B)`: permutations of `α` fixing every point outside `B`. -/
abbrev PermsIn := {φ : Equiv.Perm α // ∀ x, x ∉ B → φ x = x}

/-- A partial bijection on `B`, as its set of entries `x ↦ y`. -/
def IsPTab (f : Finset (α × α)) : Prop :=
  (∀ e ∈ f, ∀ e' ∈ f, (e.1 = e'.1 ∨ e.2 = e'.2) → e = e') ∧ ∀ e ∈ f, e.1 ∈ B ∧ e.2 ∈ B

/-- The partial bijections (tables) on `B`. -/
abbrev PTab := {f : Finset (α × α) // IsPTab α B f}

/-- The synthesis map `E |f⟩ = |T_f⟩` (all table sizes at once). -/
noncomputable def synth : Matrix (PermsIn α B) (PTab α B) ℂ :=
  fun φ f => if ∀ e ∈ f.1, φ.1 e.1 = e.2 then
    1 / (Real.sqrt ((B.card - f.1.card).factorial : ℝ) : ℂ) else 0

/-- Restriction to the tables of size `≤ r` (`r < 0` meaning none). -/
noncomputable def sizeLeDiag (r : ℕ) : Matrix (PTab α B) (PTab α B) ℂ :=
  Matrix.diagonal (fun f => if f.1.card ≤ r then 1 else 0)

/-- Restriction to the tables of size exactly `r`. -/
noncomputable def sizeEqDiag (r : ℕ) : Matrix (PTab α B) (PTab α B) ℂ :=
  Matrix.diagonal (fun f => if f.1.card = r then 1 else 0)

/-- The Moore–Penrose inverse of a Hermitian matrix (inverse on its range, `0` on its kernel). -/
noncomputable def hermPinv {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) : Matrix n n ℂ :=
  hA.cfc (fun x => if x = 0 then 0 else x⁻¹)

/-- `G^{-1/2}` on the range of a positive semidefinite Hermitian `G`, `0` on its kernel. -/
noncomputable def hermInvSqrt {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) : Matrix n n ℂ :=
  hA.cfc (fun x => if x ≤ 0 then 0 else (Real.sqrt x)⁻¹)

/-- The orthogonal projector onto `ℋ_{≤r} = span{|T_f⟩ : |f| ≤ r}`:
`M (M†M)^+ M†` with `M = E · 1[|f| ≤ r]`. -/
noncomputable def projLe (r : ℕ) : Matrix (PermsIn α B) (PermsIn α B) ℂ :=
  let M := synth α B * sizeLeDiag α B r
  M * hermPinv (Matrix.isHermitian_conjTranspose_mul_self M) * Mᴴ

/-- `Π_r`, the projector onto `ℋ_r = ℋ_{≤r} ⊖ ℋ_{≤r−1}`. -/
noncomputable def projLevel (r : ℕ) : Matrix (PermsIn α B) (PermsIn α B) ℂ :=
  projLe α B r - (if r = 0 then 0 else projLe α B (r - 1))

/-- `Γ_r = Π_r E_r` (as a map from the size-`r` tables). -/
noncomputable def gammaLevel (r : ℕ) : Matrix (PermsIn α B) (PTab α B) ℂ :=
  projLevel α B r * synth α B * sizeEqDiag α B r

/-- `Ṽ_r = Γ_r† G_r^{-1/2}`, `G_r = Γ_r Γ_r†`. -/
noncomputable def cmLevel (r : ℕ) : Matrix (PTab α B) (PermsIn α B) ℂ :=
  (gammaLevel α B r)ᴴ * hermInvSqrt (Matrix.isHermitian_mul_conjTranspose_self (gammaLevel α B r))

/-- The compression isometry `J_B = Ṽ = ⊕_{r=0}^{|B|} Ṽ_r` of [CM26, Theorem 4.2]. -/
noncomputable def cmJ : Matrix (PTab α B) (PermsIn α B) ℂ :=
  ∑ r ∈ Finset.range (B.card + 1), cmLevel α B r

/-- `⟨f| J_B |π|_B⟩` for a raw set of entries `f` and a permutation `π` of `α` mapping `B` onto
itself (`0` if `f` is not a table on `B` or `π` does not restrict to a permutation of `B`). -/
noncomputable def cmEntry (f : Finset (α × α)) (π : Equiv.Perm α) : ℂ :=
  if hf : IsPTab α B f then
    (if hπ : ∃ φ : PermsIn α B, ∀ x ∈ B, φ.1 x = π x then cmJ α B ⟨f, hf⟩ (Classical.choose hπ)
     else 0)
  else 0

end CM

variable {k : ℕ}

/-- The table `D_p` of a database restricted to the inputs in `B` (the table `D_{p,𝔅}`). -/
noncomputable def tableOf (D : Finset (Entry k)) (p : PIdx k) (B : Finset (HVtx k)) :
    Finset (HVtx k × HVtx k) :=
  (D.filter (fun e => e.1 = p ∧ e.2.1 ∈ B)).image (fun e => (e.2.1, e.2.2))

/-- The combined sign `h(u)` of a coordinate. -/
def hOf (hA hB : SignFn k) : HCoord k → ℤ
  | Sum.inl x => (hA x : ℤ)
  | Sum.inr x => (hB x : ℤ)

/-- `⟨S| F |h_A, h_B⟩ = 2^{-M/2} h(S)` with `h(S) = Π_{u ∈ S} h(u)`, `M = |𝒳| = 2N³`: the
Fourier (Hadamard) transform of the coordinate-sign register. -/
noncomputable def fourierEntry (S : Finset (HCoord k)) (hA hB : SignFn k) : ℂ :=
  (Real.sqrt ((2 : ℝ) ^ (2 * 2 ^ (3 * k))))⁻¹ * ((∏ u ∈ S, hOf hA hB u : ℤ) : ℂ)

/-- The nonempty blocks of `θ`. -/
noncomputable def blocks (θ : Labeling k) : Finset (Finset (HVtx k)) :=
  Finset.univ.image (blockOf θ)

/-- `J₊ |(π_p), h_A, h_B⟩ = (⊗_p J_V |π_p⟩) ⊗ 2^{-M/2} Σ_S h(S) |S⟩`, as a matrix
`Rec₊ ← ℋ₊`. -/
noncomputable def jY : Matrix (YRec k) (YESParam k) ℂ :=
  fun r ω => (∏ p : PIdx k, cmEntry (HVtx k) Finset.univ (tableOf r.1.1 p Finset.univ) (ω.1 p)) *
    fourierEntry r.1.2 ω.2.1 ω.2.2

/-- `J₋ |(π_p), h_A, h_B, θ⟩ = |θ⟩ ⊗ (⊗_p ⊗_{𝔅 ≠ ∅ block of θ} J_𝔅 |π_p|_𝔅⟩) ⊗
2^{-M/2} Σ_S h(S) |S⟩`, as a matrix `Rec₋ ← ℋ₋`. -/
noncomputable def jN : Matrix (NRec k) (NOSupp k) ℂ :=
  fun r ω => if r.1.1 = ω.1.2.2.2 then
    (∏ p : PIdx k, ∏ B ∈ blocks ω.1.2.2.2,
      cmEntry (HVtx k) B (tableOf r.1.2.1 p B) (ω.1.1 p)) *
      fourierEntry r.1.2.2 ω.1.2.1 ω.1.2.2.1
    else 0

/-- `Π₊ = J₊ J₊†`. -/
noncomputable def piY : Matrix (YRec k) (YRec k) ℂ := jY (k := k) * (jY (k := k))ᴴ

/-- `Π₋ = J₋ J₋†`. -/
noncomputable def piN : Matrix (NRec k) (NRec k) ℂ := jN (k := k) * (jN (k := k))ᴴ

/-- `Q_{+,a} = (I − P_{+,a}) Dec_{+,a} P_{+,a}`. -/
noncomputable def qY (a : Addr k (3 * k)) : Matrix (YRec k) (YRec k) ℂ :=
  (1 - projAddrY a) * decY a * projAddrY a

/-- `Q_{−,a} = (I − P_{−,a}) Dec_{−,a} P_{−,a}`. -/
noncomputable def qN (a : Addr k (3 * k)) : Matrix (NRec k) (NRec k) ℂ :=
  (1 - projAddrN a) * decN a * projAddrN a

end QMA2ClassicalSep.Main


