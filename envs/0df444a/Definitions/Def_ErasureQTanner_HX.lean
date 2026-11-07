-- Prove2me | Definitions.Def_ErasureQTanner_HX
-- name    : ErasureQTanner_HX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:08:17.309057+00:00
-- url     : https://prove2.me/theorems/c481bcdf-4850-442f-8eda-70adbde2da7c
-- title:
--   The check matrices $H_X,H_Z$ and the CSS objects $C_X$, $C_Z$, $C_X^\perp$, $C_Z^\perp$, $\mathrm{decode}(\mathcal C,\varepsilon)$
-- statement:
--   Every row of $H_X$ is indexed by a vertex of $V_{00}\cup V_{11}$ and a basis word of its tensor code, namely that word on the local view of the vertex and zero elsewhere. Likewise $H_Z$, with $V_{01}\cup V_{10}$. The CSS objects are $C_X=\ker H_X$, $C_Z=\ker H_Z$, with $C_X^\perp$, $C_Z^\perp$ the row spaces, and
--   $$\mathrm{decode}(\mathcal C,\varepsilon)=1\iff S_{C_X}(\varepsilon)\subseteq C_Z^\perp\text{ and }S_{C_Z}(\varepsilon)\subseteq C_X^\perp.$$
--
--   **Formalization Note** The orthogonality $H_XH_Z^{\mathsf T}=0$ holds for every complex and all local codes and bases (proved in the mission's sanity file), and it is also a clause of the goal.
-- source:
--   H. D. Pfister, O. Sprumont, G. Zémor, Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels, STOC 2027 submission (manuscript sha256 bf7a84a5…), §2, pp.3–4; §4, pp.6–7; §6, p.14

import Mathlib
import Definitions.Def_QAlgorithms_Defs_TensorCode
import Definitions.Def_ErasureQTanner_LRData
import Definitions.Def_ErasureQTanner_LocalCodes
import Definitions.Def_ErasureQTanner_covered

set_option autoImplicit false

namespace ErasureQTanner

/-- The classical code with parity-check matrix `H`: Pfister, Sprumont, Zémor, STOC 2027 submission (manuscript sha256
bf7a84a5…), §2, p.4: "The matrix `H_X` is the parity-check matrix of a classical code `C_X`". -/
def checkKer {R ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix R ι (ZMod 2)) : Submodule (ZMod 2) (ι → ZMod 2) :=
  LinearMap.ker H.mulVecLin

/-- The row space of `H`, which is the paper's `C_X^⊥` for `H = H_X` (§2, p.4). -/
def checkRows {R ι : Type*} (H : Matrix R ι (ZMod 2)) : Submodule (ZMod 2) (ι → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range fun r => H r)

/-- `decode(C, ε) = 1` (§6, p.14): "`decode(C, ε) = 1` if `S_{C_X}(ε) ⊆ C_Z^⊥` and `S_{C_Z}(ε) ⊆ C_X^⊥`". -/
def cssDecodes {R R' ι : Type*} [Fintype ι] [DecidableEq ι] (HX : Matrix R ι (ZMod 2)) (HZ : Matrix R' ι (ZMod 2))
    (x : ι → Bool) : Prop :=
  covered (checkKer HX) x ≤ checkRows HZ ∧ covered (checkKer HZ) x ≤ checkRows HX

variable {Δ : ℕ}

/-- The X-check matrix: §4, p.6: "The local views of the vertices `V00` and the vertices `V11` support the X-check
equations (or X-generators) that make up the rows of `H_X`." A row is a pair (vertex, basis index). -/
noncomputable def HX (Γ : LRData Δ) (L : LocalCodes Δ) : Matrix ((Γ.G × Fin L.r00) ⊕ (Γ.G × Fin L.r11)) Γ.Square (ZMod 2) :=
  Sum.elim (fun r => Γ.push .v00 r.1 (L.b00 r.2)) (fun r => Γ.push .v11 r.1 (L.b11 r.2))

/-- The Z-check matrix: §4, p.6: "The local views of the vertices `V10 ∪ V01` likewise host the Z-check equations." -/
noncomputable def HZ (Γ : LRData Δ) (L : LocalCodes Δ) : Matrix ((Γ.G × Fin L.r01) ⊕ (Γ.G × Fin L.r10)) Γ.Square (ZMod 2) :=
  Sum.elim (fun r => Γ.push .v01 r.1 (L.b01 r.2)) (fun r => Γ.push .v10 r.1 (L.b10 r.2))

end ErasureQTanner


