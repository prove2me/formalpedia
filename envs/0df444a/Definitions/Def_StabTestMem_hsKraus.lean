-- Prove2me | Definitions.Def_StabTestMem_hsKraus
-- name    : StabTestMem_hsKraus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:11:07.420533+00:00
-- url     : https://prove2.me/theorems/b155a969-5e7a-4427-8d61-bb408a4758d8
-- title:
--   Kraus operator $K^\beta_{s,b}$ of the hidden-shift sample (Algorithm 3)
-- statement:
--   **Algorithm 3** (stabilizer hidden-shift sample) takes a prefix $(a,r)\in\mathbb F_2^{2k}\times\mathbb F_2^m$, a phase bit $\beta\in\mathbb F_2$ and one copy of $|\psi\rangle$; it prepares an $m$-qubit register $q$ and a control qubit $c$ in $|+\rangle$, applies $F(t)=P_{a_Xr,\,a_Zt}$ (if $c=0$) or $G(t)=I_k\otimes Z(t)=P_{0\,0,\,0\,t}$ (if $c=1$) controlled on $q=t$, the phase $i^{\beta+t\cdot r}$ on $c=0$, Hadamards on $q,c$, and measures $(s,b)$. The operator applied to the copy for outcome $(s,b)$ is
--
--   $$K^{\beta}_{s,b}=\frac{1}{2^{m+1}}\sum_{t\in\mathbb F_2^m}(-1)^{t\cdot s}\Big(i^{\beta+t\cdot r}F(t)+(-1)^bG(t)\Big).$$
--
--   **Formalization Note** $\beta+t\cdot r$ is an integer exponent of $i$ (integer inner product of $0/1$ vectors); the signs depend only on residues mod $2$.
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), Algorithm 3, p. 26; Eq. (44), p. 28; p. 31

import Definitions.Def_StabTestMem_weyl
import Definitions.Def_StabTestMem_concat

namespace StabTestMem

open QAlgorithms

/-- **Kraus operator of the stabilizer hidden-shift sample (Algorithm 3) for outcome `(s, b)`.**
Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), Algorithm 3, p. 26, and p. 31 (= Eq. (44), p. 28): "The Kraus operator corresponding to
outcome (s, b) from Algorithm 3 is K^β_{s,b} = (1/2^{m+1}) Σ_{t∈F_2^m} (−1)^{t·s} (i^{β+t·r} F(t)
+ (−1)^b G(t))", with `F(t) = F_{a,r}(t) = P_{a_X r, a_Z t}` and `G(t) = I_k ⊗ Z(t) = P_{0 0, 0 t}`.

This is the operator applied to the input copy when Algorithm 3 (Hadamards on an `m`-qubit
register `q` and a control qubit `c`, the controlled Paulis `F(t)` on `c = 0` and `G(t)` on
`c = 1`, the phase `i^{β + t·r}` on `c = 0`, Hadamards again, measure `q, c`) records `(s, b)`.

**Formalization Note.** `β + t·r` in the exponent of `i` is the **integer** `β.val + Σ_j t_j r_j`
(inner product of 0/1 vectors as integers, as in Eq. (40)); `(−1)^{t·s}` and `(−1)^b` depend only on
residues mod 2. `F(t)` and `G(t)` are the Weyl operators of `concat a r t` and `concat 0 0 t`. -/
noncomputable def hsKraus {k m : ℕ} (a : CutRankSched.Pauli k) (r : Fin m → ZMod 2) (β : ZMod 2)
    (s : Fin m → ZMod 2) (b : ZMod 2) : Matrix (Qubits (k + m)) (Qubits (k + m)) ℂ :=
  ((2 : ℂ) ^ (m + 1))⁻¹ • ∑ t : Fin m → ZMod 2,
    (-1 : ℂ) ^ (∑ j, t j * s j).val •
      (Complex.I ^ (β.val + ∑ j, (t j).val * (r j).val) • weyl (concat a r t) +
        (-1 : ℂ) ^ b.val • weyl (concat (0 : CutRankSched.Pauli k) 0 t))

end StabTestMem


