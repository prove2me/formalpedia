-- Prove2me | Definitions.Def_OptQJunta_Supplement_phaseMasked
-- name    : OptQJunta_Supplement_phaseMasked
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:14:44.435389+00:00
-- url     : https://prove2.me/theorems/d018ed60-c41b-4893-abb1-38a95588f612
-- title:
--   Phase-masked unitaries $U_{f,g}$ and the ensemble $\mathbb U(p)$ (Definition 5.7)
-- statement:
--   Fix $M\ge2$, $r\ge1$ and $n=r+M$: an $r$-qubit address register and an $M$-qubit data register. For an address function $f:\{0,1\}^r\to[M]$ and a phase mask $g=(g_x)_{x\in\{0,1\}^r}$ of unit complex numbers, the **phase-masked unitary** (Definition 5.7) is
--
--   $$
--   U_{f,g}=\sum_{x\in\{0,1\}^r}g_x\,|x\rangle\langle x|\otimes Z_{f(x)},\qquad U_{f,g}|x,z\rangle=g_x(-1)^{z_{f(x)}}|x,z\rangle,
--   $$
--
--   where $Z_j$ is Pauli $Z$ on the $j$th data qubit. For $p\in\Delta([M])$, the ensemble $\mathbb U(p)$ draws $f(x)$ i.i.d. from $p$ and $g_x$ i.i.d. uniform on the unit circle, independently, so that
--
--   $$
--   \mathbb E_{U_{f,g}\sim\mathbb U(p)}[h(U_{f,g})]=\sum_f\Big(\prod_xp(f(x))\Big)\frac1{(2\pi)^{2^r}}\int_{[0,2\pi)^{2^r}}h\big(U_{f,(e^{i\theta_x})_x}\big)\,d\theta .
--   $$
--
--   This is the hard ensemble of the forward-only and channel lower bounds and the subject of Theorem 5.11.
--
--   **Formalization Note** Qubits are `Fin (r + M)` from $0$: address qubit $i$ is position $i$, and data qubit $j$ is position $r+j$. The phase mask is a function into $\mathbb C$; in the ensemble it is $e^{i\theta_x}$.
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), §5.4.1, p.65, Definition 5.7 (Eq. (35))

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace OptQJunta.Supplement

open QAlgorithms

/-- The address `x ∈ {0,1}^r` of a basis string of `n = r + M` qubits: its first `r` bits (Bao, Gao,
Yao, *Optimal Quantum Junta Testing*, preprint, version of November 3, 2026, sha256 a97d09a4…, §5.4.1,
p.65: "We index the address qubits by `[r]` and the `j`th data qubit by `r + j`").

**Formalization Note** Qubits are `Fin (r + M)` from `0`: address qubit `i` is position `i < r`, and
data qubit `j : Fin M` is position `r + j` (`Fin.natAdd r j`). -/
def addrOf {r M : ℕ} (w : Qubits (r + M)) : Qubits r :=
  fun i => w (Fin.castAdd M i)

/-- **Definition 5.7** (Phase-masked unitary; Bao–Gao–Yao preprint, version of November 3, 2026,
sha256 a97d09a4…, p.65, Eq. (35)): for an address function `f : {0,1}^r → [M]` and a phase mask
`g = (g_x)_{x ∈ {0,1}^r}`, `U_{f,g} = Σ_x g_x |x⟩⟨x| ⊗ Z_{f(x)}`, i.e. the diagonal unitary with
`U_{f,g}|x, z⟩ = g_x (−1)^{z_{f(x)}} |x, z⟩` (the address register first, then the `M` data qubits).

**Formalization Note** `g` is a function into `ℂ`; the ensemble uses `g_x = e^{iθ_x}` on the unit
circle `𝕋`, which makes `U_{f,g}` unitary. -/
noncomputable def phaseMasked {r M : ℕ} (f : Qubits r → Fin M) (g : Qubits r → ℂ) :
    Matrix (Qubits (r + M)) (Qubits (r + M)) ℂ :=
  Matrix.diagonal fun w =>
    g (addrOf w) * (if w (Fin.natAdd r (f (addrOf w))) then -1 else 1)

/-- The ensemble average `E_{U_{f,g} ∼ 𝕌(p)}[h(U_{f,g})]` (Bao–Gao–Yao preprint, version of
November 3, 2026, sha256 a97d09a4…, §5.4.1, p.65): the values `f(x)` are i.i.d. `∼ p` and the phases
`g_x` are i.i.d. uniform (Haar) on `𝕋`, i.e. `g_x = e^{iθ_x}` with `θ_x` uniform on `[0, 2π)`,
independently of `f`:
`Σ_f (Π_x p(f(x))) · (2π)^{−2^r} ∫_{[0,2π)^{2^r}} h(U_{f, (e^{iθ_x})_x}) dθ`. -/
noncomputable def ensembleAvg {r M : ℕ} (p : Fin M → ℝ)
    (h : Matrix (Qubits (r + M)) (Qubits (r + M)) ℂ → ℝ) : ℝ :=
  ∑ f : Qubits r → Fin M, (∏ x, p (f x)) *
    (((2 * Real.pi) ^ (2 ^ r))⁻¹ *
      ∫ θ in Set.univ.pi (fun _ : Qubits r => Set.Ico (0 : ℝ) (2 * Real.pi)),
        h (phaseMasked f fun x => Complex.exp ((θ x : ℂ) * Complex.I)))

end OptQJunta.Supplement


