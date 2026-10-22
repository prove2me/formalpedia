-- Prove2me | Definitions.Def_ChannelRandomization_PostProc_Setting
-- name    : ChannelRandomization_PostProc_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:27:39.373034+00:00
-- url     : https://prove2.me/theorems/4ba33aef-1674-4c0c-b9f3-f74549e5539a
-- title:
--   pp. 3–15 — Hermitian maps, s and ⟨·,·⟩, block C*-algebras, L(A,B), Pos/CP/EB, admissible families (Definition 1), P(A,B), P*(A,B), 𝒞(A,B), ‖·‖_⋄ (5), ‖·‖^⋄ (7), deficiency (Definition 3)
-- statement:
--   This file sets up the objects of §2–§3.2 of Jenčová, *Randomization theorems for quantum channels*.
--
--   **Hilbert spaces and maps.** A finite-dimensional Hilbert space is $H=\mathbb C^{h}$ with its standard orthonormal basis $\{|i\rangle\}$, and $B(H)$ is the algebra of $h\times h$ complex matrices. The space $\mathcal L(H,K)$ consists of the **Hermitian** linear maps $\phi:B(H)\to B(K)$, i.e. those with $\phi(x^*)=\phi(x)^*$; these are exactly the real-linear maps $B_h(H)\to B_h(K)$. For $\phi\in\mathcal L(H,H)$ put
--
--   $$s(\phi)=\sum_{i,j}\langle i,\phi(|i\rangle\langle j|)\,j\rangle ,$$
--
--   and define the duality between $\mathcal L(H,K)$ and $\mathcal L(K,H)$ by $\langle\phi,\psi\rangle=s(\phi\circ\psi)$.
--
--   **C*-algebras.** A C*-algebra $\mathcal A\subseteq B(H)$ is $\mathcal A=\bigoplus_k B(H_k)$ with $H=\bigoplus_k H_k$, the blocks spanned by basis vectors: a labelling $c$ of the basis vectors by block indices gives $\mathcal A=\{x : x_{ij}=0 \text{ whenever } c(i)\neq c(j)\}$. Constant labels give $B(H)$, injective labels the diagonal algebra $\mathbb D_n$. $\mathfrak S(\mathcal A)$ is the set of density matrices in $\mathcal A$. For algebras $\mathcal A\subseteq B(H)$, $\mathcal B\subseteq B(K)$, $\mathcal L(\mathcal A,\mathcal B)$ is the subspace of $\phi\in\mathcal L(H,K)$ with $\phi=E_{\mathcal B}\circ\phi\circ E_{\mathcal A}$ ($E$ the trace-preserving conditional expectations): the range of $\phi$ lies in $\mathcal B$ and $\phi$ vanishes on the Hilbert–Schmidt orthogonal complement of $\mathcal A$.
--
--   **Cones.** $Pos$ is the cone of positive maps ($\phi(B(H)^+)\subseteq B(K)^+$), $CP$ the completely positive maps ($\phi\otimes \mathrm{id}_F$ positive for every finite-dimensional $F$), and $EB$ the entanglement-breaking maps $a\mapsto\sum_i\rho_i\,\mathrm{Tr}\,F_i a$ with $\rho_i,F_i\ge0$. An **admissible family of positive cones** (Definition 1) is a family of closed convex cones $\mathcal P(H,K)\subseteq\mathcal L(H,K)$, one for every pair of finite-dimensional Hilbert spaces, such that
--
--   1. $EB\subseteq\mathcal P\subseteq Pos$;
--   2. $\mathcal P\circ\mathcal P\subseteq\mathcal P$;
--   3. $CP\circ\mathcal P\circ CP\subseteq\mathcal P$.
--
--   For algebras $\mathcal A,\mathcal B$: $\mathcal P(\mathcal A,\mathcal B)=\mathcal P(H,K)\cap\mathcal L(\mathcal A,\mathcal B)$; $\mathcal P^*(\mathcal A,\mathcal B)$ is the dual of $\mathcal P(\mathcal B,\mathcal A)$ inside $\mathcal L(\mathcal A,\mathcal B)$, $\{\phi\in\mathcal L(\mathcal A,\mathcal B):\langle\phi,\psi\rangle\ge0\ \forall\psi\in\mathcal P(\mathcal B,\mathcal A)\}$; $\mathcal C(\mathcal A,\mathcal B)$ is the set of trace-preserving elements of $\mathcal P(\mathcal A,\mathcal B)$ (the $\mathcal P$-channels); and $\Phi_{I,\sigma}:a\mapsto(\mathrm{Tr}\,a)\sigma$. Write $\le$ for the order of $\mathcal P(\mathcal A,\mathcal B)$ and $\le^*$ for that of $\mathcal P^*(\mathcal A,\mathcal B)$.
--
--   **Norms.** For $\phi\in\mathcal L(\mathcal A,\mathcal B)$,
--
--   $$\|\phi\|_\diamond=\inf_{\alpha\in\mathcal C(\mathcal A,\mathcal B)}\inf\{\lambda>0:-\lambda\alpha\le\phi\le\lambda\alpha\},\qquad \|\phi\|^\diamond=\inf_{\sigma\in\mathfrak S(\mathcal B)}\inf\{\lambda>0:-\lambda\Phi_{I,\sigma}\le^*\phi\le^*\lambda\Phi_{I,\sigma}\},$$
--
--   formulas (5) and (7) of the paper: these are the base-section norms of $\mathcal C(\mathcal A,\mathcal B)$ and of its dual section.
--
--   **Deficiency** (Definition 3). Let $\Phi\in\mathcal C(\mathcal A,\mathcal B)$, $\Psi\in\mathcal C(\mathcal A,\mathcal B')$, $\epsilon\ge0$ and $\mathcal D$ a C*-algebra. $\Psi$ is $(\epsilon,\mathcal D)$-post-processing deficient with respect to $\Phi$, $\Psi\succeq_{\epsilon,\mathcal D}\Phi$, if for every $\Gamma\in\mathcal P^*(\mathcal D,\mathcal A)$ and every $\alpha\in\mathcal C(\mathcal B,\mathcal D)$ there is $\alpha'\in\mathcal C(\mathcal B',\mathcal D)$ with
--
--   $$\langle\alpha\circ\Phi,\Gamma\rangle\le\langle\alpha'\circ\Psi,\Gamma\rangle+\epsilon\|\Gamma\|^\diamond ,$$
--
--   and $\Psi\succeq_\epsilon\Phi$ if this holds for every $\mathcal D$.
--
--   These objects are the vocabulary of the randomization theorem for post-processings (Theorem 3) and of the norm duality it rests on.
--
--   **Formalization Note.** Dimensions are natural numbers and $H=\mathbb C^h$; this lets Definition 1 quantify over all pairs of spaces, and every finite-dimensional Hilbert space is unitarily $\mathbb C^h$. Maps are $\mathbb C$-linear maps on all matrices, with Hermiticity as a separate predicate (`IsHermMap`), so $s$ is literally the page's sum; Lean takes its real part, which is the sum itself for Hermitian maps. A C*-algebra is encoded by a block label `Fin h → ℕ`, which is the paper's representation $\bigoplus_k B(H_k)\subseteq B(\bigoplus_k H_k)$ with blocks aligned to the fixed basis. "Proper cone" is encoded by closedness of the cone (in the pointwise topology, which on a finite-dimensional space is the norm topology); pointedness and solidity follow from $EB\subseteq\mathcal P\subseteq Pos$. The norms are `sInf` in $\mathbb R$; their sets are nonempty and bounded below by 0 whenever the dimensions are positive, and in dimension 0 both sides of every statement collapse to 0.
-- source:
--   Jenčová, Randomization theorems for quantum channels, arXiv:1404.3900v1, pp. 3–9, 14–15: §2 (p. 3), §2.1 (pp. 4–5, s, ⟨·,·⟩, L(A,B)), §2.2 (pp. 6–8, Pos, CP, EB, Definition 1, P(A,B), P*(B,A)), §2.3 (p. 9, 𝒞(A,B), Φ_{I,σ}, (5), (7)), Definition 3 (pp. 14–15)

import Mathlib

namespace ChannelRandomization.PostProc

open scoped Matrix ComplexOrder

/-- B(H) for H = ℂ^n with its fixed orthonormal basis (p. 3). -/
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- Ambient type of linear maps B(H) → B(K); L(H,K) is the real subspace of Hermitian ones (p. 4). -/
abbrev Map (h k : ℕ) := Mat h →ₗ[ℂ] Mat k

/-- p. 4: φ is a Hermitian map, i.e. it sends B_h(H) into B_h(K). -/
def IsHermMap {h k : ℕ} (φ : Map h k) : Prop := ∀ x : Mat h, φ xᴴ = (φ x)ᴴ

/-- p. 4: s(φ) = Σ_{i,j} ⟨i, φ(|i⟩⟨j|) j⟩ (real for Hermitian φ; the real part is taken). -/
noncomputable def s {h : ℕ} (φ : Map h h) : ℝ := (∑ i, ∑ j, φ (Matrix.single i j 1) i j).re

/-- p. 4: the duality ⟨φ, ψ⟩ = s(φ ∘ ψ), φ ∈ L(H,K), ψ ∈ L(K,H). -/
noncomputable def pair {h k : ℕ} (φ : Map h k) (ψ : Map k h) : ℝ := s (φ ∘ₗ ψ)

/-- p. 3: the C*-algebra A = ⊕_k B(H_k) ⊆ B(H), H = ⊕_k H_k, with the blocks aligned to the fixed
basis: `c i` is the block of basis vector i. Constant `c` gives B(H); injective `c` gives 𝔻_n. -/
def BlockAlg {h : ℕ} (c : Fin h → ℕ) : Set (Mat h) := {x | ∀ i j, c i ≠ c j → x i j = 0}

/-- p. 5: L(A,B), the φ ∈ L(H,K) with φ = E_B ∘ φ ∘ E_A (range in B, kills the Hilbert–Schmidt
orthogonal complement of A). -/
def InL {h k : ℕ} (A : Fin h → ℕ) (B : Fin k → ℕ) (φ : Map h k) : Prop :=
  IsHermMap φ ∧ (∀ x, φ x ∈ BlockAlg B) ∧
    ∀ x : Mat h, (∀ b ∈ BlockAlg A, (x * b).trace = 0) → φ x = 0

/-- p. 4: 𝔖(A), the states (density matrices) of A. -/
def States {h : ℕ} (A : Fin h → ℕ) : Set (Mat h) :=
  {σ | σ ∈ BlockAlg A ∧ σ.PosSemidef ∧ σ.trace = 1}

/-- p. 6: positive maps, φ(B(H)⁺) ⊆ B(K)⁺. -/
def IsPositiveMap {h k : ℕ} (φ : Map h k) : Prop :=
  ∀ x : Mat h, x.PosSemidef → (φ x).PosSemidef

/-- φ ⊗ id_F on B(H ⊗ F), F = ℂ^f, applied blockwise. -/
def ampl {h k : ℕ} (φ : Map h k) (f : ℕ)
    (X : Matrix (Fin h × Fin f) (Fin h × Fin f) ℂ) : Matrix (Fin k × Fin f) (Fin k × Fin f) ℂ :=
  fun p q => φ (fun i j => X (i, p.2) (j, q.2)) p.1 q.1

/-- p. 7: completely positive maps, φ ⊗ id_F positive for every finite-dimensional F. -/
def IsCP {h k : ℕ} (φ : Map h k) : Prop :=
  ∀ (f : ℕ) (X : Matrix (Fin h × Fin f) (Fin h × Fin f) ℂ), X.PosSemidef →
    (ampl φ f X).PosSemidef

/-- pp. 6–7: entanglement-breaking maps a ↦ Σ_i ρ_i Tr F_i a with ρ_i, F_i ≥ 0. -/
def IsEB {h k : ℕ} (φ : Map h k) : Prop :=
  ∃ (n : ℕ) (ρ : Fin n → Mat k) (F : Fin n → Mat h), (∀ i, (ρ i).PosSemidef) ∧
    (∀ i, (F i).PosSemidef) ∧ ∀ a, φ a = ∑ i, (F i * a).trace • ρ i

/-- Definition 1, p. 7: an admissible family of positive cones. "Proper" is encoded by closedness;
pointedness and solidity follow from EB ⊆ P ⊆ Pos. -/
structure AdmissibleFamily where
  cone : (h k : ℕ) → PointedCone ℝ (Map h k)
  herm : ∀ (h k : ℕ) (φ : Map h k), φ ∈ cone h k → IsHermMap φ
  closed : ∀ h k : ℕ,
    IsClosed ((fun φ : Map h k => (⇑φ : Mat h → Mat k)) '' (cone h k : Set (Map h k)))
  eb_mem : ∀ (h k : ℕ) (φ : Map h k), IsEB φ → φ ∈ cone h k
  pos_of_mem : ∀ (h k : ℕ) (φ : Map h k), φ ∈ cone h k → IsPositiveMap φ
  comp_mem : ∀ (h k l : ℕ) (φ : Map h k) (ψ : Map k l), φ ∈ cone h k → ψ ∈ cone k l →
    ψ ∘ₗ φ ∈ cone h l
  cp_comp_mem : ∀ (h' h k k' : ℕ) (α : Map h' h) (φ : Map h k) (β : Map k k'),
    IsCP α → IsCP β → φ ∈ cone h k → β ∘ₗ φ ∘ₗ α ∈ cone h' k'

/-- p. 8: P(A,B) = P(H,K) ∩ L(A,B). -/
def coneOn (P : AdmissibleFamily) {h k : ℕ} (A : Fin h → ℕ) (B : Fin k → ℕ) : Set (Map h k) :=
  {φ | φ ∈ P.cone h k ∧ InL A B φ}

/-- p. 8: P*(A,B), the dual of P(B,A) in L(A,B) with respect to ⟨·,·⟩. -/
def dualCone (P : AdmissibleFamily) {h k : ℕ} (A : Fin h → ℕ) (B : Fin k → ℕ) :
    Set (Map h k) :=
  {φ | InL A B φ ∧ ∀ ψ ∈ coneOn P B A, 0 ≤ pair φ ψ}

/-- p. 9: 𝒞(A,B), the trace-preserving elements of P(A,B) (P-channels). -/
def channels (P : AdmissibleFamily) {h k : ℕ} (A : Fin h → ℕ) (B : Fin k → ℕ) :
    Set (Map h k) :=
  {φ | φ ∈ coneOn P A B ∧ ∀ x, (φ x).trace = x.trace}

/-- p. 11 (Lemma 4): CP-channels between the algebras A and B. -/
def cpChannels {h k : ℕ} (A : Fin h → ℕ) (B : Fin k → ℕ) : Set (Map h k) :=
  {φ | IsCP φ ∧ InL A B φ ∧ ∀ x, (φ x).trace = x.trace}

/-- p. 9: Φ_{I,σ} : a ↦ (Tr a) σ. -/
noncomputable def replacer {h k : ℕ} (σ : Mat k) : Map h k :=
  LinearMap.smulRight (Matrix.traceLinearMap (Fin h) ℂ ℂ) σ

/-- p. 9, (5): ‖φ‖_⋄ = inf_{α ∈ 𝒞(A,B)} inf{λ > 0 : −λα ≤ φ ≤ λα}. -/
noncomputable def diamond (P : AdmissibleFamily) {h k : ℕ} (A : Fin h → ℕ) (B : Fin k → ℕ)
    (φ : Map h k) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ ∃ α ∈ channels P A B,
    (t : ℂ) • α - φ ∈ coneOn P A B ∧ φ + (t : ℂ) • α ∈ coneOn P A B}

/-- p. 9, (7): ‖φ‖^⋄ = inf_{σ ∈ 𝔖(B)} inf{λ > 0 : −λΦ_{I,σ} ≤* φ ≤* λΦ_{I,σ}}. -/
noncomputable def dualDiamond (P : AdmissibleFamily) {h k : ℕ} (A : Fin h → ℕ)
    (B : Fin k → ℕ) (φ : Map h k) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ ∃ σ ∈ States B,
    (t : ℂ) • replacer σ - φ ∈ dualCone P A B ∧ φ + (t : ℂ) • replacer σ ∈ dualCone P A B}

/-- Definition 3, pp. 14–15: Ψ ⪰_{ε,D} Φ. -/
def PostDeficientIn (P : AdmissibleFamily) {a b b' d : ℕ} (ε : ℝ) (A : Fin a → ℕ)
    (B : Fin b → ℕ) (B' : Fin b' → ℕ) (D : Fin d → ℕ) (Φ : Map a b) (Ψ : Map a b') : Prop :=
  ∀ Γ ∈ dualCone P D A, ∀ α ∈ channels P B D, ∃ α' ∈ channels P B' D,
    pair (α ∘ₗ Φ) Γ ≤ pair (α' ∘ₗ Ψ) Γ + ε * dualDiamond P D A Γ

/-- Definition 3, p. 15: Ψ ⪰_ε Φ, i.e. Ψ ⪰_{ε,D} Φ for every C*-algebra D. -/
def PostDeficient (P : AdmissibleFamily) {a b b' : ℕ} (ε : ℝ) (A : Fin a → ℕ)
    (B : Fin b → ℕ) (B' : Fin b' → ℕ) (Φ : Map a b) (Ψ : Map a b') : Prop :=
  ∀ (d : ℕ) (D : Fin d → ℕ), PostDeficientIn P ε A B B' D Φ Ψ

end ChannelRandomization.PostProc


