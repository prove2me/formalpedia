-- Prove2me | Definitions.Def_DQILocal_Recon_BPQM
-- name    : DQILocal_Recon_BPQM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:07:56.799843+00:00
-- url     : https://prove2.me/theorems/be7abcb0-985c-480e-9887-2b760a070697
-- title:
--   Depth-$t$ BPQM over $\mathbb Z_q$ as a POVM, its symbol-node unitaries, and its tree threshold
-- statement:
--   **Belief propagation with quantum messages** (BPQM) decodes the root of $\mathcal T_t$ by applying node operations from the leaves to the root and measuring once.
--
--   1. *Check node.* The messages of the $D-1$ child symbols are combined two at a time, in index order: on qudits with spectra $\lambda$ (first) and $\mu$ (second) it applies the complete Kraus family $\{W_\delta^\dagger\}_{\delta\in\mathbb Z_q}$, $W_\delta:|l\rangle\mapsto|l+\delta,l\rangle$; the label $\delta$ is recorded and the spectrum becomes $\nu_\delta$. After the last child it applies $|z\rangle\mapsto|-z\rangle$ (spectrum $R\nu$).
--   2. *Symbol node.* The symbol's own qudit (spectrum $p$) is combined with each child check's message in index order: a unitary $U_{\lambda,\mu}$ with $U_{\lambda,\mu}(|\psi^\lambda_y\rangle\otimes|\psi^\mu_y\rangle)=|\psi^{\lambda*\mu}_y\rangle\otimes|0\rangle$ for all $y$ is applied and the second qudit is discarded; the spectrum becomes $\lambda*\mu$.
--   3. *Root.* The root message is measured in the basis $|\mu_y\rangle=q^{-1/2}\sum_z\omega^{yz}|z\rangle$.
--
--   The spectra, and hence the unitaries, depend on the earlier labels. The resulting POVM element is $E_y=\sum_{\text{records}}K_{\mathrm{rec}}^\dagger|\mu_y\rangle\langle\mu_y|K_{\mathrm{rec}}$. A `BPQMChoice` is any family of unitaries $U_{\lambda,\mu}$ with the displayed property.
--
--   The **tree threshold of BPQM** is the supremum, in $[0,\infty]$, of the $\beta\ge0$ at which the success probability of depth-$t$ BPQM for the root tends to one as $t\to\infty$ (for every choice of unitaries).
--
--   **Formalization Note** The paper fixes the symbol-node unitary only through its property, so it is a parameter. Unitarity is required for every pair of vectors (so BPQM is a measurement also on records of probability zero), the mapping property for probability vectors. A message is a list with one entry per record: the spectrum and the adjoint Kraus kernel, evaluated on configurations of the subtree. The threshold is defined from BPQM's own success, not from $P_t$.
-- source:
--   Augustino et al., Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with Local Quantum Decoders, STOC 2027 submission (manuscript sha256 c861b07d…), §3.3 (pp. 19–21, "Larger alphabets" p. 21, threshold p. 20); Lemma 4.1, p. 23; proof of Proposition 4.3, pp. 24–25

import Mathlib
import Definitions.Def_DQILocal_Recon_Spectra
import Definitions.Def_DQILocal_Recon_Decoder
import Definitions.Def_DQILocal_Recon_TreeCode

namespace DQILocal.Recon

open scoped BigOperators ComplexOrder
open Filter Topology

/-- **A choice of symbol-node unitaries for BPQM.**
Augustino et al., *Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with
Local Quantum Decoders*, STOC 2027 submission (manuscript sha256 c861b07d…), §3.3, p. 20 ("a unitary
that depends on `a` and `b` maps this state to `|ψ_y(ab)⟩|0⟩` for both values of `y`") and
"Larger alphabets", p. 21; Lemma 4.1(1), p. 23.

For every pair of spectra `(λ, μ)` a unitary `U λ μ` on two qudits (first factor kept, second
discarded) with `U λ μ (|ψ^λ_y⟩ ⊗ |ψ^μ_y⟩) = |ψ^{λ∗μ}_y⟩ ⊗ |0⟩` for every `y ∈ ℤ_q`, whenever `λ`
and `μ` are probability vectors.

**Formalization Note.** The paper fixes this unitary only through the displayed property; the BPQM
statements quantify over every such choice. Unitarity is required for every pair of real vectors,
so that BPQM is a measurement even on records of probability zero; the displayed property is
required for probability vectors only. -/
structure BPQMChoice (q : ℕ) [NeZero q] where
  /-- The symbol-node unitary for the spectra `(λ, μ)`. -/
  U : (ZMod q → ℝ) → (ZMod q → ℝ) → Matrix (ZMod q × ZMod q) (ZMod q × ZMod q) ℂ
  /-- Each `U λ μ` is unitary. -/
  unitary : ∀ lam mu, U lam mu ∈ Matrix.unitaryGroup (ZMod q × ZMod q) ℂ
  /-- `U λ μ (|ψ^λ_y⟩ ⊗ |ψ^μ_y⟩) = |ψ^{λ∗μ}_y⟩ ⊗ |0⟩`. -/
  maps : ∀ lam mu, IsProbVec lam → IsProbVec mu → ∀ y : ZMod q,
    (U lam mu).mulVec (fun sl => psi lam y sl.1 * psi mu y sl.2) =
      fun ze => psi (conv lam mu) y ze.1 * (if ze.2 = 0 then 1 else 0)

/-- A BPQM message: one entry per classical record, holding the spectrum of the outgoing qudit and
the adjoint `K†` of the record's Kraus operator, as a kernel `K†(x, z)` from the outgoing qudit's
basis state `|z⟩` to configurations `x` of the qudits below (only the coordinates in the subtree
matter). -/
abbrev BPQMMsg (q : ℕ) := List ((ZMod q → ℝ) × ((List ℕ → ZMod q) → ZMod q → ℂ))

namespace BPQM

variable {q : ℕ} [NeZero q]

/-- A leaf, or the own qudit of a symbol `v`: spectrum `p`, Kraus operator the identity. -/
def leafMsg (p : ZMod q → ℝ) (v : List ℕ) : BPQMMsg q :=
  [(p, fun x z => if x v = z then 1 else 0)]

/-- **Check-node step (Lemma 4.1(2), p. 23).** Combine the accumulated message (spectrum `λ`, first
qudit) with the next child (spectrum `μ`, second qudit) by the complete Kraus family
`{W_δ†}_{δ ∈ ℤ_q}`, `W_δ : |l⟩ ↦ |l + δ, l⟩`; the record gains `δ` and the spectrum becomes `ν_δ`.
The new adjoint is `(K₁† ⊗ K₂†) W_δ`, i.e. `x, z ↦ K₁†(x, z + δ) K₂†(x, z)`. -/
noncomputable def checkStep (L₁ L₂ : BPQMMsg q) : BPQMMsg q :=
  L₁.flatMap fun a => L₂.flatMap fun b => (Finset.univ : Finset (ZMod q)).toList.map fun δ =>
    (nuDelta a.1 b.1 δ, fun x z => a.2 x (z + δ) * b.2 x z)

/-- Check node: the children combined two at a time in index order. -/
noncomputable def checkFold : List (BPQMMsg q) → BPQMMsg q
  | [] => []
  | L :: Ls => Ls.foldl checkStep L

/-- After the last child of a check: the unitary `|z⟩ ↦ |-z⟩` (spectrum `Rν`, p. 21, p. 24). -/
def flipMsg (L : BPQMMsg q) : BPQMMsg q :=
  L.map fun a => (refl a.1, fun x z => a.2 x (-z))

/-- **Symbol-node step (Lemma 4.1(1), p. 23; p. 21).** Combine the accumulated message (spectrum
`λ`) with the next child check's message (spectrum `μ`): apply `U λ μ` and discard the second qudit,
i.e. the complete Kraus family `{(I ⊗ ⟨e|) U λ μ}_{e ∈ ℤ_q}`; the spectrum becomes `λ ∗ μ`. -/
noncomputable def symStep (U : BPQMChoice q) (L₁ L₂ : BPQMMsg q) : BPQMMsg q :=
  L₁.flatMap fun a => L₂.flatMap fun b => (Finset.univ : Finset (ZMod q)).toList.map fun e =>
    (conv a.1 b.1, fun x z => ∑ s : ZMod q, ∑ l : ZMod q,
      a.2 x s * b.2 x l * star (U.U a.1 b.1 (z, e) (s, l)))

/-- The message sent up by the symbol `v` at depth `d` of `T_t` whose subtree has height `h`
(leaves at height `0`): its own qudit combined, in index order, with the messages of its child
checks `v ++ [a]`; each child check combines the messages of its child symbols `v ++ [a, b]`,
`b < D - 1`, and then applies `|z⟩ ↦ |-z⟩`. -/
noncomputable def symMsg (k D : ℕ) (p : ZMod q → ℝ) (U : BPQMChoice q) :
    ℕ → ℕ → List ℕ → BPQMMsg q
  | 0, _, v => leafMsg p v
  | h + 1, d, v => (List.range (branchT k d)).foldl
      (fun acc a => symStep U acc (flipMsg (checkFold ((List.range (D - 1)).map
        fun b => symMsg k D p U h (d + 1) (v ++ [a, b])))))
      (leafMsg p v)

/-- The Fourier basis vector `|μ_y⟩ = q^{-1/2} Σ_z ω^{yz} |z⟩` (p. 25). -/
noncomputable def fourierVec (y z : ZMod q) : ℂ :=
  (1 / (Real.sqrt q : ℂ)) * omega q (y * z)

end BPQM

/-- **Depth-`t` BPQM over `ℤ_q` for the root of `T_t`** (§3.3 "Larger alphabets", p. 21; proof of
Proposition 4.3, pp. 24–25), as a POVM on the qudits of `T_t` with outcomes `y ∈ ℤ_q`.

The node operations are applied from the leaves to the root (`BPQM.symMsg k D p U t 0 []`), every
label is kept as a classical record, and the root message is measured in the basis `|μ_y⟩` (the
inverse quantum Fourier transform followed by a computational-basis measurement). The POVM element
is `E_y = Σ_records K_rec† |μ_y⟩⟨μ_y| K_rec`.

**Formalization Note.** The spectra, and so the unitaries used, depend on the earlier records. The
qudits of `T_t` are indexed by its symbols; a configuration is extended by `0` off `T_t` before the
kernels (which only read coordinates in `T_t`) are evaluated. -/
noncomputable def bpqm {q : ℕ} [NeZero q] (k D t : ℕ) (p : ZMod q → ℝ) (U : BPQMChoice q) :
    ZMod q → Matrix (treeSyms k D t → ZMod q) (treeSyms k D t → ZMod q) ℂ := by
  classical
  exact fun y x x' =>
    let ext : (treeSyms k D t → ZMod q) → List ℕ → ZMod q :=
      fun x s => if h : s ∈ treeSyms k D t then x ⟨s, h⟩ else 0
    let w : ((ZMod q → ℝ) × ((List ℕ → ZMod q) → ZMod q → ℂ)) → (treeSyms k D t → ZMod q) → ℂ :=
      fun a x => ∑ z : ZMod q, a.2 (ext x) z * BPQM.fourierVec y z
    ((BPQM.symMsg k D p U t 0 []).map fun a => w a x * star (w a x')).sum

/-- **The tree threshold of BPQM** (§3.3, pp. 20–21: "Its threshold is the largest `σ_β`, or
equivalently the largest `β`, at which the overlaps tend to zero"; Corollary 4.11, p. 29): the
supremum, in `[0, ∞]`, of the `β ≥ 0` at which the success probability of depth-`t` BPQM for the
root of `T_t` tends to one as `t → ∞`, for every choice of symbol-node unitaries.

**Formalization Note.** Defined from the BPQM success probability itself, not from `P_t`. -/
noncomputable def bpqmThreshold (k D q : ℕ) [NeZero q] (f : ZMod q → ℝ) : ENNReal :=
  ⨆ (β : ℝ) (_ : 0 ≤ β ∧ ∀ U : BPQMChoice q,
      Tendsto (fun t => treeSuccess k D t (gibbsWeight q f β) (bpqm k D t (gibbsWeight q f β) U))
        atTop (𝓝 1)),
    ENNReal.ofReal β

end DQILocal.Recon


