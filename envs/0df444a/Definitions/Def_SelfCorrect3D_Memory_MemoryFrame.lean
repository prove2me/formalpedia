-- Prove2me | Definitions.Def_SelfCorrect3D_Memory_MemoryFrame
-- name    : SelfCorrect3D_Memory_MemoryFrame
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:35:24.299927+00:00
-- url     : https://prove2.me/theorems/faf59a60-e6d3-42d0-bc2b-af579b1390ce
-- title:
--   Logical operators, decoder and code isometry of a one-qubit CSS code
-- statement:
--   For a CSS code with one logical qubit, a **memory frame** consists of
--
--   1. logical supports $x_L\in\ker H_z$ and $z_L\in\ker H_x$ with $x_L\cdot z_L=1$, giving anticommuting logical operators $X_L=X^{x_L}$, $Z_L=Z^{z_L}$;
--   2. a **decoder**: maps $f_Z:\mathbb F_2^{m_x}\to\mathbb F_2^n$ and $f_X:\mathbb F_2^{m_z}\to\mathbb F_2^n$ such that $H_xf_Z(\sigma_Z)=\sigma_Z$ and $H_zf_X(\sigma_X)=\sigma_X$ for every achievable syndrome, defining the Pauli corrections $\mathcal O_Z(\sigma_Z)=Z^{f_Z(\sigma_Z)}$, $\mathcal O_X(\sigma_X)=X^{f_X(\sigma_X)}$;
--   3. an isometry $V:\mathbb C^2\to\mathcal H$ onto the code space ($\Pi_0V=V$) with $X_LV=V\sigma^x$ and $Z_LV=V\sigma^z$.
--
--   Through $|a\rangle\otimes|\sigma\rangle\mapsto\mathcal O(\sigma)V|a\rangle$, $\mathcal O(\sigma)=\mathcal O_X(\sigma_X)\mathcal O_Z(\sigma_Z)$, a frame realizes the factorization $\mathcal H_S=\mathcal H_{\log}\otimes\mathcal H_{\mathrm{syn}}$ used to define the thermal encoding and the decoding.
--
--   **Formalization Note** $\sigma^x,\sigma^z$ are the Pauli matrices on $\mathbb C^2$ with basis $|0\rangle,|1\rangle$. The decoder is unconstrained off the achievable syndromes.
-- source:
--   Balasubramanian, Davydova, Lin, A passive self-correcting quantum memory in three dimensions, arXiv:2605.10943, §2.5, p. 20 (Definition 2.3) and p. 21

import Mathlib
import Definitions.Def_SelfCorrect3D_Memory_CSSCode_syndProjX
import Definitions.Def_SelfCorrect3D_Memory_CSSCode_syndProjZ
open Matrix

namespace SelfCorrect3D.Memory

/-- **Logical operators, decoder and code-space isometry of a CSS code with one logical qubit.**
Balasubramanian, Davydova, Lin, *A passive self-correcting quantum memory in three dimensions*, arXiv:2605.10943, §2.5, p. 20 ("Call X_L and Z_L the logical operators
associated to the encoded qubit"; Definition 2.3: "logical operators (X_L, Z_L) and Pauli
corrections output by the decoder O_Z(σ_Z) = Z^{f_Z(σ_Z)} and O_X(σ_X) = X^{f_X(σ_X)}") and p. 21
(`𝓗_S = 𝓗_log ⊗ 𝓗_syn`).

Fields: logical supports `x_L ∈ ker H_z`, `z_L ∈ ker H_x` with `x_L · z_L = 1`
(`X_L = X^{x_L}`, `Z_L = Z^{z_L}` anticommute); decoder maps `f_Z`, `f_X` returning a correction
with the given syndrome, for every achievable syndrome; an isometry `V : ℂ² → 𝓗` onto the code
space (syndrome `0`) with `X_L V = V σˣ` and `Z_L V = V σᶻ`.

**Formalization Note.** `σˣ`, `σᶻ` are the Pauli matrices on `ℂ^{ZMod 2}` (index `0` = `|0⟩`).
For a code with one logical qubit such an isometry exists and is unique up to a phase. The decoder
is arbitrary off the achievable syndromes (it is never used there). -/
structure MemoryFrame {n mX mZ : ℕ} (C : CSSCode n mX mZ) : Type where
  /-- Support of the logical `X_L = X^{x_L}`. -/
  xL : Fin n → ZMod 2
  /-- Support of the logical `Z_L = Z^{z_L}`. -/
  zL : Fin n → ZMod 2
  /-- `X_L` commutes with every Z-check. -/
  hxL : C.HZ.mulVec xL = 0
  /-- `Z_L` commutes with every X-check. -/
  hzL : C.HX.mulVec zL = 0
  /-- `X_L` and `Z_L` anticommute. -/
  hxz : xL ⬝ᵥ zL = 1
  /-- Decoder for Z errors: support `f_Z(σ_Z)` of the Z-type correction `O_Z(σ_Z)`. -/
  fZ : (Fin mX → ZMod 2) → Fin n → ZMod 2
  /-- Decoder for X errors: support `f_X(σ_X)` of the X-type correction `O_X(σ_X)`. -/
  fX : (Fin mZ → ZMod 2) → Fin n → ZMod 2
  /-- `O_Z(σ_Z)` has X-check syndrome `σ_Z`. -/
  hfZ : ∀ σZ ∈ C.achX, C.HX.mulVec (fZ σZ) = σZ
  /-- `O_X(σ_X)` has Z-check syndrome `σ_X`. -/
  hfX : ∀ σX ∈ C.achZ, C.HZ.mulVec (fX σX) = σX
  /-- The encoding isometry of the logical qubit into the code space. -/
  V : Matrix (Fin n → ZMod 2) (ZMod 2) ℂ
  /-- `V` is an isometry. -/
  hV : Vᴴ * V = 1
  /-- `V` maps into the code space (syndrome `0`). -/
  hVcode : C.syndProjX 0 * C.syndProjZ 0 * V = V
  /-- `X_L V = V σˣ`. -/
  hVX : pauliX xL * V = V * Matrix.of fun a b : ZMod 2 => if a = b + 1 then (1 : ℂ) else 0
  /-- `Z_L V = V σᶻ`. -/
  hVZ : pauliZ zL * V = V * Matrix.diagonal fun a : ZMod 2 => (-1 : ℂ) ^ a.val

end SelfCorrect3D.Memory


