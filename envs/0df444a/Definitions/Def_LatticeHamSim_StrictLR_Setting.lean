-- Prove2me | Definitions.Def_LatticeHamSim_StrictLR_Setting
-- name    : LatticeHamSim_StrictLR_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:54:23.874866+00:00
-- url     : https://prove2.me/theorems/7bc93b16-8c40-4092-ab05-10b783e8adfa
-- title:
--   §2, pp. 8–9 and Appendix C.1–C.2, C.4, pp. 21–22, 26 — local operators, H = Σ_X h_X, H_Ω, O(t; J), dist(X,Y), C_B(X,t) (18), D_B(X,t) (19), linked chains
-- statement:
--   Let $\Lambda$ be a finite set of **sites** equipped with a metric $\mathrm{dist}$, and attach to every site a copy of $\mathbb{C}^q$. Operators are complex matrices indexed by configurations $\sigma : \Lambda \to \{0, \dots, q-1\}$, i.e. operators on $\bigotimes_{x \in \Lambda} \mathbb{C}^q$ in the product basis. All norms $\|\cdot\|$ are operator norms.
--
--   1. **Support.** An operator $M$ is *supported on* $X \subseteq \Lambda$ if $M = m \otimes \mathbb{1}_{\Lambda \setminus X}$ for an operator $m$ on the sites of $X$: the entry $M_{\sigma\tau}$ is $0$ unless $\sigma$ and $\tau$ agree outside $X$, and is then $m_{\sigma|_X, \tau|_X}$. An operator supported on $\emptyset$ is a scalar multiple of the identity.
--   2. **Heisenberg evolution.** For an operator $O$ and a Hermitian $J$, $O(t; J) := e^{iJt} O e^{-iJt}$. Given a family $(h_X)_{X \subseteq \Lambda}$ of operators (one for **every** subset $X$), the Hamiltonian is $H = \sum_{X \subseteq \Lambda} h_X$ and, for $\Omega \subseteq \Lambda$, $H_\Omega = \sum_{Z \subseteq \Omega} h_Z$. One writes $O(t) = O(t; H)$.
--   3. **Distances.** For nonempty finite sets $X, Y$ of sites, $\mathrm{dist}(X, Y) = \min_{x \in X, y \in Y} \mathrm{dist}(x, y)$.
--   4. **Overlap.** $X \sim Y$ means $X \cap Y \neq \emptyset$.
--   5. **Commutator quantities.** For a fixed operator $B$,
--   $$C_B(X, t) = \sup_{A \in \mathcal{A}_X,\ \|A\| \le 1} \|[A(t), B]\|, \qquad D_B(X, t) = \|[h_X(t), B]\|,$$
--   where $\mathcal{A}_X$ is the algebra of operators supported on $X$.
--   6. **Linked chains.** A $k$-tuple $(Z_1, \dots, Z_k)$ of sets of sites is *linked* from $X$ if $X \sim Z_1 \sim Z_2 \sim \cdots \sim Z_k$, that is $X \sim Z_1$ and $Z_j \sim Z_{j+1}$ for each $j$. The linked sum is
--   $$L_k(X) = \sum_{Z_1, \dots, Z_k \,:\, \text{linked}} \ \prod_{j=1}^{k} \|h_{Z_j}\|,$$
--   with $L_0(X) = 1$ (the empty chain).
--
--   These are the objects of Appendix C of the paper, in which the Lieb–Robinson bounds for lattice Hamiltonians are proved; every statement of this mission is phrased in them.
--
--   **Formalization Note** Objects 1–5 (`SupportedOn`, `evolve`, `H`, `setDist`, `meets`, `CB`, `DB`) are the shared definitions of `LatticeHamSim.CommLR.Setting`, which this module imports; it adds $H_\Omega$ (`HOmega`) and the linked chains (`chain`, `Linked`, `linkedSum`). Sites are any finite metric space, with the same local dimension $q$ at every site; the paper's qubits are $q = 2$. The norm is Mathlib's $L^2$ operator norm on matrices (`Matrix.Norms.L2Operator`), not the entrywise or Frobenius norm. `setDist X Y` is the minimum above when $X$ and $Y$ are nonempty and $0$ otherwise; the statements that use it remain true under this convention, because an operator supported on $\emptyset$ is a scalar. $C_B$ is a real supremum: its defining set is nonempty ($A = 0$) and, when $H$ is Hermitian, bounded above by $2\|B\|$, so the supremum is the paper's. `HOmega h Ω` includes the term $h_\emptyset$, as in $\sum_{Z \subseteq \Omega} h_Z$.
-- source:
--   Haah, Hastings, Kothari and Low, Quantum algorithm for simulating real time evolution of lattice Hamiltonians, arXiv:1801.03922v4, p. 8, §2 (dist, diam); p. 9, Lemma 5 (H_Ω); p. 21, Appendix C.1 (O(t; J)); p. 22, Appendix C.2, displays (18), (19) and X ∼ Y; p. 26, Appendix C.4 (H_Ω = Σ_{Z⊆Ω} h_Z, "linked")

import Mathlib
import Definitions.Def_LatticeHamSim_CommLR_Setting
open scoped Matrix.Norms.L2Operator

namespace LatticeHamSim.StrictLR

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {q : ℕ}

/-- The restricted Hamiltonian `H_Ω = ∑_{Z ⊆ Ω} h_Z` (the term `Z = ∅` included). -/
def HOmega (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (Ω : Finset Λ) :
    Matrix (Λ → Fin q) (Λ → Fin q) ℂ :=
  ∑ Z ∈ Finset.univ.filter (fun Z => Z ⊆ Ω), h Z

instance (X Y : Finset Λ) : Decidable (LatticeHamSim.CommLR.meets X Y) :=
  inferInstanceAs (Decidable (X ∩ Y).Nonempty)

/-- The chain `X, Z₁, …, Z_k`: index `0` is `X`, index `j + 1` is `Z_{j+1}`. -/
def chain {k : ℕ} (X : Finset Λ) (Z : Fin k → Finset Λ) : Fin (k + 1) → Finset Λ :=
  Fin.cons X Z

/-- `Z₁, …, Z_k` is linked from `X`: `X ∼ Z₁ ∼ Z₂ ∼ ⋯ ∼ Z_k` (vacuous for `k = 0`). -/
def Linked {k : ℕ} (X : Finset Λ) (Z : Fin k → Finset Λ) : Prop :=
  ∀ j : Fin k, LatticeHamSim.CommLR.meets (chain X Z j.castSucc) (Z j)

open Classical in
/-- `∑_{Z₁, …, Z_k : linked} ∏_{j=1}^k ‖h_{Z_j}‖`, over all `k`-tuples of sets of sites
linked from `X`; equal to `1` for `k = 0` (the empty chain). -/
noncomputable def linkedSum (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (X : Finset Λ) (k : ℕ) : ℝ :=
  ∑ Z : Fin k → Finset Λ, (∏ j : Fin k, ‖h (Z j)‖) * (if Linked X Z then 1 else 0)

end LatticeHamSim.StrictLR


