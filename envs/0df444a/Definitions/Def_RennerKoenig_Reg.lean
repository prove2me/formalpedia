-- Prove2me | Definitions.Def_RennerKoenig_Reg
-- name    : RennerKoenig_Reg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:43:57.28727+00:00
-- url     : https://prove2.me/theorems/3d757585-9672-4fc7-b4f2-b698116a95d0
-- title:
--   Classical register tensored with a Hilbert space, $\ell^2(\alpha,H)$
-- statement:
--   Let $H$ be a Hilbert space and $\alpha$ a set. A classical system with orthonormal basis $\{|x\rangle\}_{x\in\alpha}$, tensored with $H$, is the Hilbert sum
--
--   $$
--   \ell^2(\alpha,H)=\Big\{(v_x)_{x\in\alpha}:\ v_x\in H,\ \sum_{x}\|v_x\|^2<\infty\Big\}.
--   $$
--
--   Every classical register in the mission lives in such a space, so a classical part may have any range.
--
--   **Formalization Note** The register is always the outer factor, whichever side the paper writes it on.
-- source:
--   Renner–König, Universally Composable Privacy Amplification Against Quantum Adversaries, arXiv:quant-ph/0403133v2, §2.2, pp.3-4

import Mathlib

namespace RennerKoenig

/-- **Classical register tensored with a Hilbert space.** Renner–König, *Universally Composable Privacy Amplification Against Quantum Adversaries*,
arXiv:quant-ph/0403133v2, §2.2, pp.3-4:
the classical system has orthonormal basis `|x⟩`, `x ∈ α`, so `ℂ^α ⊗ H` is the Hilbert sum
`ℓ²(α, H)` of copies of `H` indexed by `α`.

**Formalization Note** `α` is any type, so a register needs no finite or countable range. The
register is always the outer factor, whichever side the page writes it on. -/
abbrev Reg (α : Type*) (H : Type*) [NormedAddCommGroup H] := lp (fun _ : α => H) 2

end RennerKoenig


