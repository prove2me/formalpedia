-- Prove2me | Definitions.Def_NoLocalBroadcast_Broadcast_Model
-- name    : NoLocalBroadcast_Broadcast_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:34:24.761328+00:00
-- url     : https://prove2.me/theorems/56dca7f0-862f-46eb-95e6-992b4eec59bb
-- title:
--   Definitions 1–6 (pp. 1–3) — local channels, broadcast states, local broadcastability, CC and CQ states, I, I_CQ, I_CC, Holevo χ, and the state σ̃ of Theorem 3's proof
-- statement:
--   The objects of the mission: bipartite states, local channels, broadcast states, local broadcastability, classical-quantum and classical-classical states, and the three measures of correlation $I$, $I_{CQ}$, $I_{CC}$.
--
--   Throughout, $A$ and $B$ are finite-dimensional systems, with orthonormal bases indexed by finite sets $a$ and $b$; a state of $A\otimes B$ is a positive semidefinite matrix $\rho$ on $a\times b$ with $\operatorname{Tr}\rho=1$. Every map is a channel, i.e. trace preserving and completely positive (footnote [21]), given by a finite Kraus family $\{K_k\}$ with $\sum_k K_k^\dagger K_k=\mathbb 1$ and acting as $X\mapsto\sum_k K_kXK_k^\dagger$.
--
--   1. **Local channels.** For channels $\Lambda_A:A\to A_1$ (Kraus operators $K_k$) and $\Gamma_B:B\to B_1$ (Kraus operators $L_l$), the channel $\Lambda_A\otimes\Gamma_B$ has the Kraus operators $K_k\otimes L_l$.
--   2. **Reductions of a two-copy state.** An operator $\sigma$ on $(AA')(BB')$, with $A'$ a copy of $A$ and $B'$ a copy of $B$, has the reductions $\sigma_X=\operatorname{Tr}_{A'B'}\sigma$ and $\sigma_Y=\operatorname{Tr}_{AB}\sigma$ to the copies $X=AB$ and $Y=A'B'$.
--   3. **Broadcast state (Definition 5).** $\sigma$ is a broadcast state for $\rho$ if it is a state and $\sigma_X=\sigma_Y=\rho$.
--   4. **Locally broadcastable (Definition 6).** $\rho$ is LB if there are channels $\Theta_A:A\to AA'$ and $\Theta_B:B\to BB'$ such that $(\Theta_A\otimes\Theta_B)[\rho]$ is a broadcast state for $\rho$.
--   5. **Classical-classical (Definition 1(iii)).** $\rho$ is CC if there are orthonormal families $\{|i\rangle\}$ of $A$ and $\{|j\rangle\}$ of $B$ and a joint probability distribution $p_{ij}$ with
--   $$\rho=\sum_{ij}p_{ij}\,|i\rangle\langle i|\otimes|j\rangle\langle j|.$$
--   6. **Classical-quantum (Definition 1(ii)).** $\rho$ is CQ if $\rho=\sum_ip_i|i\rangle\langle i|\otimes\sigma_i^B$ with $\{|i\rangle\}$ orthonormal, $\{p_i\}$ a probability distribution and states $\sigma_i^B$.
--   7. **Mutual information (Definition 3).** $I(\rho_{AB})=S(\rho_A)+S(\rho_B)-S(\rho_{AB})$, where $S(\rho)=-\operatorname{Tr}\rho\log\rho$ is the von Neumann entropy and $\rho_A=\operatorname{Tr}_B\rho$, $\rho_B=\operatorname{Tr}_A\rho$.
--   8. **Measured states (Definition 2).** For a POVM $\{M_i\}_{i=1}^n$ on $A$ ($M_i\ge0$, $\sum_iM_i=\mathbb 1$), $\rho^{CQ}(\{M_i\})=(\mathcal M_A\otimes\mathrm{id}_B)[\rho]=\sum_i|i\rangle\langle i|\otimes\operatorname{Tr}_A\big((M_i\otimes\mathbb 1)\rho\big)$; for POVMs $\{M_i\}$ on $A$ and $\{N_j\}$ on $B$, $\rho^{CC}(\{M_i\},\{N_j\})=\sum_{ij}\operatorname{Tr}\big((M_i\otimes N_j)\rho\big)\,|i\rangle\langle i|\otimes|j\rangle\langle j|$.
--   9. **CQ and CC mutual information (Definition 4).**
--   $$I_{CQ}(\rho)=\max_{\{M_i\}}I\big(\rho^{CQ}(\{M_i\})\big),\qquad I_{CC}(\rho)=\max_{\{M_i\},\{N_j\}}I\big(\rho^{CC}(\{M_i\},\{N_j\})\big).$$
--   10. **Holevo quantity (Lemma 1).** $\chi(\{p_i,\sigma_i\})=S\big(\sum_ip_i\sigma_i\big)-\sum_ip_iS(\sigma_i)$.
--   11. **The state $\tilde\sigma$ of the proof of Theorem 3.** For finite registers $I,J$, a distribution $p_{ij}$ on $I\times J$ and operators $\rho^{ij}$ on $A'B'$, $\tilde\sigma=\sum_{ij}p_{ij}\,|i\rangle\langle i|_A\otimes|j\rangle\langle j|_B\otimes\rho^{ij}_{A'B'}$, read across the cut $AA':BB'$.
--
--   These are the objects every statement of the mission is about.
--
--   **Formalization Note** Systems are index types with `Fintype` and `DecidableEq`. A two-copy operator is indexed $((x,x'),(y,y'))\in(a\times a)\times(b\times b)$, so the parties are $(A,A')$ and $(B,B')$ and `mutualInfo` of it is $I(\sigma_{AA':BB'})$; `traceCopies` removes $A'B'$ and `traceOriginals` removes $AB$. `QAlgorithms.traceRight` removes the second factor and `QAlgorithms.traceLeft` the first. "Orthonormal sets" are orthonormal families indexed by `Fin k` (any size, not necessarily bases). The register of a measurement map is the computational basis of `Fin n`; the maxima of Definition 4 are `sSup` over POVMs with any finite number of outcomes (the set is nonempty and bounded above by $I(\rho)$ for a state, and the maximum is attained in finite dimension, so `sSup` is the paper's value). Entropy is `QAlgorithms.vnEntropy`, in bits. `flaggedState` is indexed $((i,x'),(j,y'))$.
-- source:
--   Piani, Horodecki & Horodecki, No-local-broadcasting theorem for quantum correlations, arXiv:0707.0848v2, pp. 1–3, Definitions 1–6, Lemma 1 (Holevo quantity), proof of Theorem 3 (σ̃); p. 5, footnote [21]

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_Ensemble

namespace NoLocalBroadcast.Broadcast

open Matrix
open scoped Kronecker

/-! ## States, local channels, broadcasting (Definitions 1, 5, 6, pp. 1, 3) -/

/-- Footnote [21], p. 5, and Observation 1, p. 2: the local channel `Λ_A ⊗ Γ_B` with
`Λ_A : A → A₁` given by the Kraus family `K` and `Γ_B : B → B₁` given by `L`. Its Kraus
operators are the Kronecker products `K k ⊗ L l`; it acts on every operator of `A ⊗ B`. -/
noncomputable def localApply {a a₁ b b₁ : Type} [Fintype a] [Fintype b] {m n : ℕ}
    (K : Fin m → Matrix a₁ a ℂ) (L : Fin n → Matrix b₁ b ℂ) :
    Matrix (a × b) (a × b) ℂ → Matrix (a₁ × b₁) (a₁ × b₁) ℂ :=
  QAlgorithms.krausApply (fun kl : Fin m × Fin n => K kl.1 ⊗ₖ L kl.2)

/-- Definition 5, p. 3: for an operator `σ` on `(A A′)(B B′)`, indexed `((x, x′), (y, y′))`,
the reduction `σ_X = Tr_{A′B′} σ` to the first copy `X = AB`. -/
def traceCopies {a b : Type} [Fintype a] [Fintype b]
    (σ : Matrix ((a × a) × (b × b)) ((a × a) × (b × b)) ℂ) : Matrix (a × b) (a × b) ℂ :=
  Matrix.of fun p q => ∑ x : a, ∑ y : b, σ ((p.1, x), (p.2, y)) ((q.1, x), (q.2, y))

/-- Definition 5, p. 3: the reduction `σ_Y = Tr_{AB} σ` to the second copy `Y = A′B′`. -/
def traceOriginals {a b : Type} [Fintype a] [Fintype b]
    (σ : Matrix ((a × a) × (b × b)) ((a × a) × (b × b)) ℂ) : Matrix (a × b) (a × b) ℂ :=
  Matrix.of fun p q => ∑ x : a, ∑ y : b, σ ((x, p.1), (y, p.2)) ((x, q.1), (y, q.2))

/-- Definition 5, p. 3: `σ` is a broadcast state for `ρ`: a state on `(A A′)(B B′)` whose
reductions to both copies are `ρ` (`σ_X = σ_Y = ρ`). -/
def IsBroadcastState {a b : Type} [Fintype a] [Fintype b]
    (ρ : Matrix (a × b) (a × b) ℂ) (σ : Matrix ((a × a) × (b × b)) ((a × a) × (b × b)) ℂ) :
    Prop :=
  QAlgorithms.IsDensityMatrix σ ∧ traceCopies σ = ρ ∧ traceOriginals σ = ρ

/-- Definition 6, p. 3: `ρ` is locally broadcastable: there are channels `Θ_A : A → AA′` and
`Θ_B : B → BB′` (finite normalized Kraus families) such that `(Θ_A ⊗ Θ_B)[ρ]` is a broadcast
state for `ρ`. -/
def IsLocallyBroadcastable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ρ : Matrix (a × b) (a × b) ℂ) : Prop :=
  ∃ (m n : ℕ) (K : Fin m → Matrix (a × a) a ℂ) (L : Fin n → Matrix (b × b) b ℂ),
    QAlgorithms.IsKrausFamily K ∧ QAlgorithms.IsKrausFamily L ∧
      IsBroadcastState ρ (localApply K L ρ)

/-- Definition 1(iii), p. 1: `ρ` is classical-classical: there are orthonormal families
`{|i⟩}` in `A` and `{|j⟩}` in `B` and a joint probability distribution `p_{ij}` with
`ρ = Σ_{ij} p_{ij} |i⟩⟨i| ⊗ |j⟩⟨j|`. -/
def IsClassicalClassical {a b : Type} [Fintype a] [Fintype b]
    (ρ : Matrix (a × b) (a × b) ℂ) : Prop :=
  ∃ (k l : ℕ) (e : Fin k → EuclideanSpace ℂ a) (f : Fin l → EuclideanSpace ℂ b)
    (p : Fin k × Fin l → ℝ),
    Orthonormal ℂ e ∧ Orthonormal ℂ f ∧ (∀ ij, 0 ≤ p ij) ∧ ∑ ij, p ij = 1 ∧
      ρ = ∑ ij, (p ij : ℂ) •
        (QAlgorithms.pureDensity (e ij.1) ⊗ₖ QAlgorithms.pureDensity (f ij.2))

/-- Definition 1(ii), p. 1: `ρ` is classical-quantum: there are an orthonormal family `{|i⟩}`
in `A`, a probability distribution `p_i` and states `σ_i` of `B` with
`ρ = Σ_i p_i |i⟩⟨i| ⊗ σ_i`. -/
def IsClassicalQuantum {a b : Type} [Fintype a] [Fintype b]
    (ρ : Matrix (a × b) (a × b) ℂ) : Prop :=
  ∃ (k : ℕ) (e : Fin k → EuclideanSpace ℂ a) (p : Fin k → ℝ) (σ : Fin k → Matrix b b ℂ),
    Orthonormal ℂ e ∧ (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧
      (∀ i, QAlgorithms.IsDensityMatrix (σ i)) ∧
      ρ = ∑ i, (p i : ℂ) • (QAlgorithms.pureDensity (e i) ⊗ₖ σ i)

/-! ## Information quantities (Definitions 2–4, pp. 1–2; Lemma 1, p. 2) -/

/-- Definition 3, p. 2: the quantum mutual information `I(ρ_{AB}) = S(A) + S(B) − S(AB)` of an
operator on `α × β` (cut between the first and the second factor), with the von Neumann entropy
`QAlgorithms.vnEntropy` in bits. `traceRight` removes `β` (giving `ρ_A`), `traceLeft` removes
`α` (giving `ρ_B`). -/
noncomputable def mutualInfo {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (X : Matrix (α × β) (α × β) ℂ) : ℝ :=
  QAlgorithms.vnEntropy (QAlgorithms.traceRight X) + QAlgorithms.vnEntropy (QAlgorithms.traceLeft X)
    - QAlgorithms.vnEntropy X

/-- Definition 2 and p. 1: the CQ state `ρ^{CQ}({M_i}) = (M_A ⊗ id_B)[ρ] = Σ_i |i⟩⟨i| ⊗ Tr_A(M_i^A ρ)`
obtained by the measurement map of the POVM `{M_i}` on `A`, the outcome written in the
computational basis of the register `Fin n`. -/
noncomputable def cqState {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {n : ℕ} (ρ : Matrix (a × b) (a × b) ℂ) (M : Fin n → Matrix a a ℂ) :
    Matrix (Fin n × b) (Fin n × b) ℂ :=
  Matrix.of fun p q =>
    if p.1 = q.1 then QAlgorithms.traceLeft ((M p.1 ⊗ₖ (1 : Matrix b b ℂ)) * ρ) p.2 q.2 else 0

/-- Definition 2 and p. 2: the CC state `ρ^{CC}({M_i},{N_j}) = (M_A ⊗ N_B)[ρ]
= Σ_{ij} p_{ij} |i⟩⟨i| ⊗ |j⟩⟨j|`, `p_{ij} = Tr(M_i^A ⊗ N_j^B ρ)`, on the registers
`Fin n × Fin n'`. -/
noncomputable def ccState {a b : Type} [Fintype a] [Fintype b] {n n' : ℕ}
    (ρ : Matrix (a × b) (a × b) ℂ) (M : Fin n → Matrix a a ℂ) (N : Fin n' → Matrix b b ℂ) :
    Matrix (Fin n × Fin n') (Fin n × Fin n') ℂ :=
  Matrix.diagonal fun ij => ((M ij.1 ⊗ₖ N ij.2) * ρ).trace

/-- Definition 4, p. 2: the CQ mutual information `I_CQ(ρ) = max_{{M_i}} I(ρ^{CQ}({M_i}))`,
the supremum over POVMs on `A` with any finite number of outcomes. -/
noncomputable def I_CQ {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ρ : Matrix (a × b) (a × b) ℂ) : ℝ :=
  sSup {x | ∃ (n : ℕ) (M : Fin n → Matrix a a ℂ), QAlgorithms.IsPOVM M ∧
    x = mutualInfo (cqState ρ M)}

/-- Definition 4, p. 2: the CC mutual information
`I_CC(ρ) = max_{{M_i},{N_j}} I(ρ^{CC}({M_i},{N_j}))`, the supremum over pairs of POVMs on `A`
and on `B` with any finite numbers of outcomes. -/
noncomputable def I_CC {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ρ : Matrix (a × b) (a × b) ℂ) : ℝ :=
  sSup {x | ∃ (n n' : ℕ) (M : Fin n → Matrix a a ℂ) (N : Fin n' → Matrix b b ℂ),
    QAlgorithms.IsPOVM M ∧ QAlgorithms.IsPOVM N ∧ x = mutualInfo (ccState ρ M N)}

/-- Lemma 1, p. 2: the Holevo quantity `χ({p_i, σ_i}) = S(Σ_i p_i σ_i) − Σ_i p_i S(σ_i)`. -/
noncomputable def holevoChi {b : Type} [Fintype b] [DecidableEq b] {k : ℕ} (p : Fin k → ℝ)
    (σ : Fin k → Matrix b b ℂ) : ℝ :=
  QAlgorithms.vnEntropy (∑ i, (p i : ℂ) • σ i) - ∑ i, p i * QAlgorithms.vnEntropy (σ i)

/-! ## The state `σ̃` of the proof of Theorem 3 (display (1), p. 3) -/

/-- Proof of Theorem 3, p. 3: `σ̃ = Σ_{ij} p_{ij} |i⟩⟨i|_A ⊗ |j⟩⟨j|_B ⊗ ρ^{ij}_{A′B′}`, with
classical registers `ι` (on `A`) and `κ` (on `B`), regrouped across the cut `AA′ : BB′`: it is
indexed `((i, x′), (j, y′))`. -/
noncomputable def flaggedState {ι κ a' b' : Type} [DecidableEq ι] [DecidableEq κ]
    (p : ι × κ → ℝ) (ρij : ι × κ → Matrix (a' × b') (a' × b') ℂ) :
    Matrix ((ι × a') × (κ × b')) ((ι × a') × (κ × b')) ℂ :=
  Matrix.of fun r s =>
    if r.1.1 = s.1.1 ∧ r.2.1 = s.2.1 then
      (p (r.1.1, r.2.1) : ℂ) * ρij (r.1.1, r.2.1) (r.1.2, r.2.2) (s.1.2, s.2.2)
    else 0

end NoLocalBroadcast.Broadcast


