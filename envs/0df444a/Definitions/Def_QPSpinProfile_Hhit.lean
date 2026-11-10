-- Prove2me | Definitions.Def_QPSpinProfile_Hhit
-- name    : QPSpinProfile_Hhit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T03:26:51.017938+00:00
-- url     : https://prove2.me/theorems/9f3c7d7e-af86-4087-836b-73c6ad2a5706
-- title:
--   $H_J$, $H_{\mathrm{hit}}(J^c)$ and the admissible sets $\mathcal J_{n,m_\star}$
-- statement:
--   For $J\subseteq[n]$, split the Hamiltonian as $H_{n,p}=H_J+H_{\mathrm{hit}}(J^c)$ with
--   $$
--   H_J=\binom np^{-1/2}\sum_{\substack{P\in\mathcal P_{n,p}\\ \mathrm{supp}(P)\subseteq J}}g_P\,P,\qquad H_{\mathrm{hit}}(J^c)=H_{n,p}-H_J ,
--   $$
--   so that $H_{\mathrm{hit}}(J^c)$ collects the interactions whose support meets $J^c$. For an integer $0\le m_\star\le n$, the **admissible sets** are $\mathcal J_{n,m_\star}=\{J\subseteq[n]:|J^c|\le m_\star\}$.
--
--   **Formalization Note** `Hhit n p J g` is indexed by the retained set $J$; the paper writes its argument as $J^c$.
-- source:
--   Al-Ghattas, Gamarnik, Kiani, Beyond light cones: State preparation complexity in quantum spin glasses, arXiv:2610.02166 (held version, sha256 a0a1ec89…), §2.2, p.22 (PDF p.25)

import Mathlib
import Definitions.Def_QPSpinProfile_hamiltonian

namespace QPSpinProfile

open Matrix

/-- The part of the Hamiltonian supported in `J`: `H_J := C(n,p)^{-1/2} ∑_{supp(P) ⊆ J} g_P P`
(arXiv:2610.02166, held version sha256 a0a1ec89…, §2.2, p.22, PDF p.25). -/
noncomputable def Hsub (n p : ℕ) (J : Finset (Fin n)) (g : PauliString n p → ℝ) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  (((Real.sqrt (n.choose p : ℝ))⁻¹ : ℝ) : ℂ) •
    ∑ P ∈ Finset.univ.filter (fun P : PauliString n p => P.supp ⊆ J), ((g P : ℝ) : ℂ) • P.mat

/-- The terms hitting `Jᶜ`: `H_hit(Jᶜ) := H_{n,p} − H_J` (arXiv:2610.02166, §2.2, p.22, PDF p.25).

**Formalization Note** Indexed by the retained set `J` (the paper writes the argument `Jᶜ`). -/
noncomputable def Hhit (n p : ℕ) (J : Finset (Fin n)) (g : PauliString n p → ℝ) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  hamiltonian n p g - Hsub n p J g

/-- The admissible sets `J_{n,m⋆} := {J ⊆ [n] : |Jᶜ| ≤ m⋆}` (arXiv:2610.02166, §2.2, p.22,
PDF p.25). -/
def admissible (n m : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun J => (Finset.univ \ J).card ≤ m)

end QPSpinProfile


