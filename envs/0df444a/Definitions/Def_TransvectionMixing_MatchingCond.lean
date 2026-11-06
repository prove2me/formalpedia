-- Prove2me | Definitions.Def_TransvectionMixing_MatchingCond
-- name    : TransvectionMixing_MatchingCond
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:19:09.258906+00:00
-- url     : https://prove2.me/theorems/f669527e-161b-4b36-a577-9a95f2cfc64f
-- title:
--   Quasi-shear matching condition, the split $B_0\sqcup B_1$ and the shears $L(A)$, $U(B)$, $\tilde U$
-- statement:
--   Let $B_0=\{1,\dots,\lfloor n/2\rfloor\}$ and $B_1=\{\lfloor n/2\rfloor+1,\dots,n\}$. In the block order $(B_0,B_1)$,
--   $$
--   L(A)=\begin{pmatrix}I_{\lfloor n/2\rfloor}&0\\A&I_{\lceil n/2\rceil}\end{pmatrix},\qquad
--   U(B)=\begin{pmatrix}I_{\lfloor n/2\rfloor}&B\\0&I_{\lceil n/2\rceil}\end{pmatrix},
--   $$
--   and a shear $\tilde U$ from $B_1\setminus\{n\}$ to $B_0\cup\{n\}$ is a matrix of the form $\begin{pmatrix}I&*&0\\0&I&0\\0&*&1\end{pmatrix}$ in the order $(B_0,B_1\setminus\{n\},\{n\})$, with arbitrary starred blocks.
--
--   For source and target sets $S,R$ and a skeleton split into three consecutive sublists $\tau=\tau_1\tau_2\tau_3$, put for each target $i\in R$
--   $$
--   S_{a,i}=\{s\in S:(s\mapsto i)\in\tau_a\}\ (a\in\{1,3\}),\qquad P_i=S\setminus(S_{1,i}\cup S_{3,i}),\qquad Q_i=S_{1,i}\cap S_{3,i}.
--   $$
--   The **matching condition** holds if, for every $i\in R$, the middle sublist contains updates matching all of $P_i$ to distinct rows of $Q_i$: there is an injection $\varphi_i:P_i\to Q_i$ with every update $p\mapsto\varphi_i(p)$ occurring in $\tau_2$.
--
--   **Formalization Note** Rows are 0-based: $B_0$ is the rows $i<\lfloor n/2\rfloor$ and the last row $n$ is `n − 1`. $L(A)$ and $U(B)$ take full $n\times n$ matrices and use only the displayed off-diagonal block.
-- source:
--   Braverman, Jain, Newman, Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over Large Fields (manuscript, sha256 217f833f…), §5.3, p.25 (B₀, B₁, L(A), U(B), Ũ); table and Lemma 5.5, p.26 (segments, S_{a,i}, P_i, Q_i, matching condition)

import Mathlib
import Definitions.Def_TransvectionMixing_walkMat

namespace TransvectionMixing

/-- `S_{a,i} = {s ∈ S : (s ↦ i) ∈ τ_a}`: the sources in `S` updating target `i` somewhere in
the sublist `τ_a` (Braverman–Jain–Newman, *Optimal Marginal Mixing for Transvection-Based
Trapdoored Matrices over Large Fields*, manuscript sha256 217f833f…, Lemma 5.5, p.26). -/
def outerSources {n N : ℕ} (S : Finset (Fin n)) (i : Fin n) (τ : Skel n N) : Finset (Fin n) :=
  S.filter (fun s => ∃ u : Fin N, (τ u).1 = (s, i))

/-- `P_i = S ∖ (S_{1,i} ∪ S_{3,i})`: sources updating `i` in neither outer sublist
(manuscript sha256 217f833f…, Lemma 5.5, p.26). -/
def Pset {n N₁ N₃ : ℕ} (S : Finset (Fin n)) (i : Fin n) (τ₁ : Skel n N₁) (τ₃ : Skel n N₃) :
    Finset (Fin n) :=
  S \ (outerSources S i τ₁ ∪ outerSources S i τ₃)

/-- `Q_i = S_{1,i} ∩ S_{3,i}`: sources updating `i` in both outer sublists (manuscript sha256
217f833f…, Lemma 5.5, p.26). -/
def Qset {n N₁ N₃ : ℕ} (S : Finset (Fin n)) (i : Fin n) (τ₁ : Skel n N₁) (τ₃ : Skel n N₃) :
    Finset (Fin n) :=
  outerSources S i τ₁ ∩ outerSources S i τ₃

/-- For the target `i`, the middle sublist `τ₂` contains updates matching all of `P_i` to
distinct rows of `Q_i`: an injection `φ : P_i → Q_i` with every `p ↦ φ(p)` occurring in `τ₂`
(manuscript sha256 217f833f…, Lemma 5.5, p.26). -/
def MatchesTarget {n N₁ N₂ N₃ : ℕ} (S : Finset (Fin n)) (i : Fin n) (τ₁ : Skel n N₁)
    (τ₂ : Skel n N₂) (τ₃ : Skel n N₃) : Prop :=
  ∃ φ : Fin n → Fin n, Set.InjOn φ ↑(Pset S i τ₁ τ₃) ∧
    ∀ p ∈ Pset S i τ₁ τ₃, φ p ∈ Qset S i τ₁ τ₃ ∧ ∃ u : Fin N₂, (τ₂ u).1 = (p, φ p)

/-- The matching condition of Lemma 5.5 for source set `S`, target set `R` and a skeleton split
into three consecutive sublists `τ₁τ₂τ₃`: every target `i ∈ R` is matched (manuscript sha256
217f833f…, Lemma 5.5, p.26). -/
def MatchingCond {n N₁ N₂ N₃ : ℕ} (S R : Finset (Fin n)) (τ₁ : Skel n N₁) (τ₂ : Skel n N₂)
    (τ₃ : Skel n N₃) : Prop :=
  ∀ i ∈ R, MatchesTarget S i τ₁ τ₂ τ₃

/-- `B₀ = {1, …, ⌊n/2⌋}` (manuscript sha256 217f833f…, §5.3, p.25); 0-based, the rows
`i < ⌊n/2⌋`. -/
def B0 (n : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => i.val < n / 2)

/-- `B₁ = {⌊n/2⌋ + 1, …, n}` (manuscript sha256 217f833f…, §5.3, p.25); 0-based, the rows
`i ≥ ⌊n/2⌋`. -/
def B1 (n : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => n / 2 ≤ i.val)

/-- `B₁ ∖ {n}` (0-based: the last row is `n − 1`), the source set of `σ₄` (p.26). -/
def B1' (n : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => n / 2 ≤ i.val ∧ i.val ≠ n - 1)

/-- `B₀ ∪ {n}` (0-based: the last row is `n − 1`), the target set of `σ₄` (p.26). -/
def B0' (n : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => i.val < n / 2 ∨ i.val = n - 1)

/-- A segment split into three consecutive sublists, `τ₁τ₂τ₃`. -/
def seg3 {n N₁ N₂ N₃ : ℕ} (τ₁ : Skel n N₁) (τ₂ : Skel n N₂) (τ₃ : Skel n N₃) :
    Skel n (N₁ + N₂ + N₃) :=
  (τ₁.append τ₂).append τ₃

/-- The lower shear `L(A) = [[I_{⌊n/2⌋}, 0], [A, I_{⌈n/2⌉}]]` for the split `B₀ ⊔ B₁`
(manuscript sha256 217f833f…, §5.3, p.25). Only the `B₁ × B₀` block of `A` is used. -/
def lowerShear {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if i = j then 1 else if n / 2 ≤ i.val ∧ j.val < n / 2 then A i j else 0

/-- The upper shear `U(B) = [[I_{⌊n/2⌋}, B], [0, I_{⌈n/2⌉}]]` (manuscript sha256 217f833f…,
§5.3, p.25). Only the `B₀ × B₁` block of `B` is used. -/
def upperShear {R : Type*} [CommRing R] {n : ℕ} (B : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if i = j then 1 else if i.val < n / 2 ∧ n / 2 ≤ j.val then B i j else 0

/-- `Ũ` is a shear from `B₁ ∖ {n}` to `B₀ ∪ {n}`: in the coordinate order
`(B₀, B₁ ∖ {n}, {n})` it is `[[I, ∗, 0], [0, I, 0], [0, ∗, 1]]` with arbitrary starred blocks
(manuscript sha256 217f833f…, §5.3, p.25). -/
def IsModShear {R : Type*} [CommRing R] {n : ℕ} (U : Matrix (Fin n) (Fin n) R) : Prop :=
  (∀ i, U i i = 1) ∧
    ∀ i j, i ≠ j → ¬ (i ∈ B0' n ∧ j ∈ B1' n) → U i j = 0

end TransvectionMixing


