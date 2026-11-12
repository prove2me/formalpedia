-- Prove2me | Definitions.Def_ImpuritySim_Occupation
-- name    : ImpuritySim_Occupation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:33:55.703669+00:00
-- url     : https://prove2.me/theorems/c358213b-e0d3-47c2-a717-f3f960c3b16e
-- title:
--   Weighted occupation statistics: $D(x)$, $e^{D/2}$, $A_I$, $\rho_I$, $F_q$, $B_I$, $C_I$, $\Delta_I$, $\Phi_{J,i}$, $M^{J\ell}$ and $e^{-\lambda D_\ell}E_\ell e^{\lambda D_\ell}$
-- statement:
--   Fix weights $\{h_d\}_{d\ge1}$ with
--   $$h_1=0,\qquad |h_{d+1}-h_d|\le1,\qquad h_d\ge0\qquad(4.2);$$
--   the ground-state choice is $h^{(\infty)}_d=d-1$ (5.1). For a Hamiltonian in the form (3.15) define, with $\lambda=1/4$ (4.5):
--
--   1. $D(x)=\sum_{i\in S_{\mathrm{bath}}}h_{d(i)}x_i$ and $D=\sum_ih_{d(i)}n_i$ (4.3), so $e^{2\lambda D}=e^{D/2}$ is diagonal in the Fock basis; the threshold set $S=\{x:D(x)\le T\}$ (4.6);
--   2. for an increasing list $I=(i_1<\dots<i_q)$ of bath modes, $A_I=a_{i_q}\cdots a_{i_1}$, $A_\emptyset=I$, $h(I)=\sum_{i\in I}h_{d(i)}$ and $\rho_I=e^{2\lambda h(I)}A_I\rho A_I^\dagger$ (4.9);
--   3. for $q=(q_0,\dots,q_L)$, $I\sim q$ means $|\{i\in I:\ell(i)=\ell\}|=q_\ell$ for all $\ell$, and
--   $$F_q=\sum_{I\sim q}e^{2\lambda h(I)}\operatorname{Tr}\Bigl(\rho\prod_{i\in I}n_i\Bigr)\quad(4.11),\qquad \alpha_q=\sum_\ell q_\ell\omega_\ell\quad(4.31);$$
--   4. the bath-replacement and hybridization contributions
--   $$B_I=\sum_{i\in I}\sum_{\substack{j:\ell(j)=\ell(i)\\ j\notin I\setminus\{i\}}}\varepsilon_I(i,j)\langle e_j,E_{\ell(i)}e_i\rangle A_{I(i\to j)}\ (4.19),\qquad C_I=\sum_{i\in I}\eta_I(i)\sum_{s=1}^{r_{\ell(i)}}\langle u_{\ell(i)s},e_i\rangle G_{\ell(i)s}A_{I\setminus\{i\}}\ (4.20),$$
--   with $\varepsilon_I(i,j)=(-1)^{\#\{k\in I\setminus\{i\}\text{ strictly between }i\text{ and }j\}}$ and $\eta_I(i)=(-1)^{\#\{k\in I:k>i\}}$, the reordering signs of p.23;
--   5. $\Delta_I=\operatorname{Re}\operatorname{Tr}(\rho A_I^\dagger[H,A_I])$ (4.21);
--   6. $\Phi_{J,i}=e^{\lambda(h(J)+h_{d(i)})}a_iA_J$ (4.23) and the correlation matrix $M^{J\ell}_{ij}=\operatorname{Tr}(\rho\Phi_{J,i}^\dagger\Phi_{J,j})$ on band-$\ell$ bath modes $i,j\notin J$, extended by zero (4.24);
--   7. $D_\ell=\sum_{d\ge1}h_d\Pi_{\ell,d}$ (3.19), the diagonal matrix of the weights on band $\ell$, and $\operatorname{Re}(e^{-\lambda D_\ell}E_\ell e^{\lambda D_\ell})$ with $\operatorname{Re}(X)=(X+X^\dagger)/2$.
--
--   These are the quantities of the occupation recursion of §4 and of Theorems 4.1 and 5.1.
--
--   **Formalization Note** Increasing lists are finite sets of bath modes; $I(i\to j)=(I\setminus\{i\})\cup\{j\}$; $\langle e_j,Ee_i\rangle=E_{ji}$ and $\langle u,e_i\rangle=\overline{u_i}$. $F_q$ uses real parts of traces (they are real for Hermitian $\rho$). Lemma 3.2's operator is defined for every $\lambda$; all other quantities use $\lambda=1/4$.
-- source:
--   Jiang–Ju–Parekh–Rayudu–Zhao, Polynomial-time classical and quantum simulation of quantum impurity models, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), (3.19), p.18; (4.1)–(4.6), p.20; (4.9)–(4.12), p.21; (4.19)–(4.21), pp.22–23; (4.23)–(4.24), p.23; (4.31), p.24; (5.1), p.26; App. B.2, p.55

import Mathlib
import Definitions.Def_ImpuritySim_BandwiseForm
import Definitions.Def_ImpuritySim_Machine

open Matrix

namespace ImpuritySim

/-!
# Weighted occupation statistics and the commutator calculus of §4

J. Jiang, N. Ju, O. Parekh, C. Rayudu, A. Zhao, *Polynomial-time classical and quantum simulation
of quantum impurity models*, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2): (3.19),
p.18; (4.1)–(4.6), p.20; (4.9)–(4.12), p.21; (4.19)–(4.21), pp.22–23; (4.23)–(4.24), p.23;
(4.31), p.24; (5.1), p.26; App. B.2, p.55.

**Formalization Note.**
* Weights `h : ℕ → ℝ` (only `h d`, `d ≥ 1`, matter); `ValidWeights h` is (4.2): `h_1 = 0`,
  `|h_{d+1} − h_d| ≤ 1` and `h_d ≥ 0` for `d ≥ 1`. `hInf d = d − 1` is `h^(∞)` (5.1).
* `D(x) = Σ_{i ∈ S_bath} h_{d(i)} x_i` (4.3) is `Dval`; the operator `D = Σ h_{d(i)} n_i` is
  diagonal in the Fock basis since `n_i = |1⟩⟨1|_i` (4.1), so `e^{2λD}` with `λ = 1/4` (4.5) is the
  diagonal matrix `expHalfD` of `e^{D(x)/2}`. The section fixes `λ = 1/4`; all `e^{2λ·}` below are
  `e^{·/2}` and `e^{λ·}` are `e^{·/4}`.
* `thresholdSet F h T = {x : D(x) ≤ T}` is `wSet` of the weights `h_{d(i)}` on bath modes and `0`
  on enlarged-impurity modes.
* Increasing lists `I = (i_1 < ⋯ < i_q)` of bath modes are finsets `I ⊆ bath`;
  `AI n I = a_{i_q} ⋯ a_{i_1}` (decreasing order), `A_∅ = I` (4.9); `hI F h I = h(I) = Σ_{i ∈ I} h_{d(i)}`;
  `rhoI F h ρ I = ρ_I = e^{2λh(I)} A_I ρ A_I†` (4.9).
* `q = (q_0, …, q_L) : Fin (L+1) → ℕ`; `compatSets F q` is `{I ⊆ bath : I ∼ q}` (4.12);
  `Fq F h ρ q = Σ_{I ∼ q} e^{2λh(I)} Tr(ρ ∏_{i ∈ I} n_i)` (4.11) (real part; the traces are real);
  `qMinus q ℓ = q − e_ℓ`; `alphaQ F q = α_q = Σ_ℓ q_ℓ ω_ℓ` (4.31).
* Signs (p.23, App. B.2): `epsSign I i j = (−1)^{#{k ∈ I∖{i} : k strictly between i and j}}`
  (replacing `a_i` by `a_j` in `a_{i_q}⋯a_{i_1}` and restoring decreasing order),
  `etaSign I i = (−1)^{#{k ∈ I : k > i}}` (moving `G` to the left of `a_{i_q}⋯`).
* `BI` is (4.19) with `I(i→j) = (I∖{i}) ∪ {j}` and `⟨e_j, E_{ℓ(i)} e_i⟩ = E j i`, `j` ranging over the
  band-`ℓ(i)` bath modes not in `I∖{i}`; `CI` is (4.20) with `⟨u_{ℓs}, e_i⟩ = conj(u_{ℓs,i})`.
* `DeltaI F ρ I = Δ_I = Re Tr(ρ A_I† [H, A_I])` (4.21).
* `PhiJ F h J i = Φ_{J,i} = e^{λ(h(J)+h_{d(i)})} a_i A_J` (4.23); `Mcorr F h ρ J ℓ` is `M^{Jℓ}` (4.24),
  `M_ij = Tr(ρ Φ_{J,i}† Φ_{J,j})` for band-`ℓ` bath modes `i, j ∉ J`, and `0` otherwise.
* `simE F h λ ℓ = e^{−λD_ℓ} E_ℓ e^{λD_ℓ}` with `D_ℓ = Σ_{d ≥ 1} h_d Π_{ℓ,d}` (3.19), the diagonal
  matrix of `h_{d(i)}` on the band-`ℓ` bath modes, so `e^{±λD_ℓ}` is diagonal; `reSimE` is its
  Hermitian part `Re(X) = (X + X†)/2` (p.18).
-/

open FermiCap.Gaussian

/-- The weight conditions (4.2): `h_1 = 0`, `|h_{d+1} − h_d| ≤ 1` and `h_d ≥ 0` for `d ≥ 1`. -/
def ValidWeights (h : ℕ → ℝ) : Prop :=
  h 1 = 0 ∧ (∀ d, 1 ≤ d → |h (d + 1) - h d| ≤ 1) ∧ ∀ d, 1 ≤ d → 0 ≤ h d

/-- The ground-state weights `h^(∞)_d = d − 1` (5.1). -/
def hInf : ℕ → ℝ := fun d => (d : ℝ) - 1

/-- `A_I = a_{i_q} ⋯ a_{i_1}` for `I = (i_1 < ⋯ < i_q)`, `A_∅ = I` (4.9). -/
noncomputable def AI (n : ℕ) (I : Finset (Fin n)) : Op n :=
  (((I.sort (· ≤ ·)).reverse).map (GaussTesting.annihilator n)).prod

/-- The fermionic sign `ε_I(i, j)` of (4.19): `(−1)` to the number of `k ∈ I∖{i}` strictly between
`i` and `j`. -/
def epsSign {n : ℕ} (I : Finset (Fin n)) (i j : Fin n) : ℂ :=
  (-1) ^ ((I.erase i).filter fun k => min i j < k ∧ k < max i j).card

/-- The fermionic sign `η_I(i)` of (4.20): `(−1)` to the number of `k ∈ I` with `k > i`. -/
def etaSign {n : ℕ} (I : Finset (Fin n)) (i : Fin n) : ℂ :=
  (-1) ^ (I.filter fun k => i < k).card

namespace BandwiseForm

variable {n : ℕ} (F : BandwiseForm n)

/-- The weight `h_{d(i)}` of a bath mode, `0` on enlarged-impurity modes. -/
def depthWeights (h : ℕ → ℝ) : Fin n → ℝ := fun i => if i ∈ F.bath then h (F.depth i) else 0

/-- `D(x) = Σ_{i ∈ S_bath} h_{d(i)} x_i` (4.3). -/
def Dval (h : ℕ → ℝ) (x : Qubits n) : ℝ := ∑ i, F.depthWeights h i * ((x i : ℕ) : ℝ)

/-- `e^{2λD} = e^{D/2}` (`λ = 1/4`, (4.5)), diagonal in the Fock basis. -/
noncomputable def expHalfD (h : ℕ → ℝ) : Op n :=
  Matrix.diagonal fun x => ((Real.exp (F.Dval h x / 2) : ℝ) : ℂ)

/-- The threshold set `S = {x : D(x) ≤ T}` (4.6). -/
noncomputable def thresholdSet (h : ℕ → ℝ) (T : ℝ) : Finset (Qubits n) :=
  wSet (F.depthWeights h) T

/-- `h(I) = Σ_{i ∈ I} h_{d(i)}` (4.9). -/
def hI (h : ℕ → ℝ) (I : Finset (Fin n)) : ℝ := ∑ i ∈ I, h (F.depth i)

/-- `ρ_I = e^{2λh(I)} A_I ρ A_I†` (4.9). -/
noncomputable def rhoI (h : ℕ → ℝ) (ρ : Op n) (I : Finset (Fin n)) : Op n :=
  ((Real.exp (F.hI h I / 2) : ℝ) : ℂ) • (AI n I * ρ * (AI n I)ᴴ)

/-- The increasing lists of bath modes consistent with `q`, `I ∼ q` (4.12). -/
noncomputable def compatSets (q : Fin (F.L + 1) → ℕ) : Finset (Finset (Fin n)) :=
  F.bath.powerset.filter fun I => ∀ ℓ : Fin (F.L + 1), (I.filter fun i => F.band i = ℓ).card = q ℓ

/-- The band-grouped weighted joint occupation `F_q = Σ_{I ∼ q} e^{2λh(I)} Tr(ρ ∏_{i ∈ I} n_i)` (4.11). -/
noncomputable def Fq (h : ℕ → ℝ) (ρ : Op n) (q : Fin (F.L + 1) → ℕ) : ℝ :=
  ∑ I ∈ F.compatSets q, Real.exp (F.hI h I / 2) *
    (ρ * ((I.sort (· ≤ ·)).map (FermiHubbardMix.numOp n)).prod).trace.re

/-- `q − e_ℓ` (4.12). -/
noncomputable def qMinus (q : Fin (F.L + 1) → ℕ) (ℓ : Fin (F.L + 1)) : Fin (F.L + 1) → ℕ :=
  Function.update q ℓ (q ℓ - 1)

/-- `α_q = Σ_ℓ q_ℓ ω_ℓ` (4.31). -/
noncomputable def alphaQ (q : Fin (F.L + 1) → ℕ) : ℝ := ∑ ℓ : Fin (F.L + 1), (q ℓ : ℝ) * F.omegaL ℓ

/-- The bath-replacement contribution `B_I` (4.19). -/
noncomputable def BI (I : Finset (Fin n)) : Op n :=
  ∑ i ∈ I, ∑ j ∈ F.bath.filter (fun j => F.band j = F.band i ∧ j ∉ I.erase i),
    (epsSign I i j * F.E j i) • AI n (insert j (I.erase i))

/-- The hybridization contribution `C_I` (4.20). -/
noncomputable def CI (I : Finset (Fin n)) : Op n :=
  ∑ i ∈ I, etaSign I i • ∑ s : Fin (F.r (F.band i)),
    star (F.u (F.band i) s i) • (F.G (F.band i) s * AI n (I.erase i))

/-- The commutator contribution `Δ_I = Re Tr(ρ A_I† [H, A_I])` (4.21). -/
noncomputable def DeltaI (ρ : Op n) (I : Finset (Fin n)) : ℝ :=
  (ρ * (AI n I)ᴴ * (F.H * AI n I - AI n I * F.H)).trace.re

/-- `Φ_{J,i} = e^{λ(h(J) + h_{d(i)})} a_i A_J` (4.23), `λ = 1/4`. -/
noncomputable def PhiJ (h : ℕ → ℝ) (J : Finset (Fin n)) (i : Fin n) : Op n :=
  ((Real.exp ((F.hI h J + h (F.depth i)) / 4) : ℝ) : ℂ) • (GaussTesting.annihilator n i * AI n J)

/-- The single-particle correlation matrix `M^{Jℓ}` on the band-`ℓ` bath modes (4.24). -/
noncomputable def Mcorr (h : ℕ → ℝ) (ρ : Op n) (J : Finset (Fin n)) (ℓ : ℕ) :
    Matrix (F.bandIdx ℓ) (F.bandIdx ℓ) ℂ :=
  fun i j => if i.1 ∉ J ∧ j.1 ∉ J then (ρ * (F.PhiJ h J i.1)ᴴ * F.PhiJ h J j.1).trace else 0

/-- `e^{−λD_ℓ} E_ℓ e^{λD_ℓ}` with `D_ℓ = Σ_{d ≥ 1} h_d Π_{ℓ,d}` (3.19). -/
noncomputable def simE (h : ℕ → ℝ) (lam : ℝ) (ℓ : ℕ) : Matrix (F.bandIdx ℓ) (F.bandIdx ℓ) ℂ :=
  Matrix.diagonal (fun i : F.bandIdx ℓ => ((Real.exp (-lam * h (F.depth i.1)) : ℝ) : ℂ)) *
    F.Eband ℓ *
    Matrix.diagonal (fun i : F.bandIdx ℓ => ((Real.exp (lam * h (F.depth i.1)) : ℝ) : ℂ))

/-- `Re(e^{−λD_ℓ} E_ℓ e^{λD_ℓ}) = (X + X†)/2`. -/
noncomputable def reSimE (h : ℕ → ℝ) (lam : ℝ) (ℓ : ℕ) : Matrix (F.bandIdx ℓ) (F.bandIdx ℓ) ℂ :=
  (1 / 2 : ℂ) • (F.simE h lam ℓ + (F.simE h lam ℓ)ᴴ)

end BandwiseForm

end ImpuritySim


