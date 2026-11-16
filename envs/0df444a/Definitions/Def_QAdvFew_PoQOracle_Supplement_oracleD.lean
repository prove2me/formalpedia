-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_Supplement_oracleD
-- name    : QAdvFew_PoQOracle_Supplement_oracleD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:17:03.674631+00:00
-- url     : https://prove2.me/theorems/be13943e-74bb-4bba-8002-bbbf1040ee62
-- title:
--   The oracle $O=(\mathrm{SG},\mathrm{Expand},\mathrm{Mix})$ of §5.1
-- statement:
--   Fix a level $t$ and write $\mathrm{RO}_t(x,y)=(u_{x,y},v_{x,y})$. The **claw state** is $|c_{x,y}\rangle\propto|u_{x,y}\rangle+|v_{x,y}\rangle$, normalized (it is $|u_{x,y}\rangle$ when $u_{x,y}=v_{x,y}$). Let
--
--   $$
--   \sigma_t=\frac1{2^t}\sum_{x}|x\rangle\langle x|\otimes|\phi_x\rangle\langle\phi_x|,\qquad
--   \rho_x=\frac1{2^{4t}}\sum_{y}|y\rangle\langle y|\otimes|c_{x,y}\rangle\langle c_{x,y}| .
--   $$
--
--   The oracle's three components at level $t$ are
--
--   1. $\mathrm{SG}_t=S^{W^{\mathrm{SG}}_t}_{\sigma_t}$;
--   2. $\mathrm{Expand}_t=\sum_x|x\rangle\langle x|\otimes S^{W^{\mathrm{Expand}}_{t,x}}_{\rho_x}$;
--   3. $\mathrm{Mix}_t=\sum_{x,y}|x,y\rangle\langle x,y|\otimes\bigl(|\phi_x\rangle\langle\phi_x|\otimes S_{|u_{x,y},v_{x,y}\rangle}+(I-|\phi_x\rangle\langle\phi_x|)\otimes I\bigr)$.
--
--   **Formalization Note** The purifications are fixed explicitly: $\sum_x2^{-t/2}|x\rangle|\phi_x\rangle\otimes|x0^{3t}\rangle$ for $\sigma_t$ (purifying register of $4t$ qubits) and $\sum_y2^{-2t}|y\rangle|c_{x,y}\rangle\otimes|y0\rangle$ for $\rho_x$ ($4t+1$ qubits). Since the $W$'s are Haar-distributed, the law of the oracle does not depend on this choice. The components are numbered $0,1,2$; other components act on zero qubits.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §5.1, pp. 32–33 (PDF pp. 34–35)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Supplement_DSample
import Definitions.Def_QAdvFew_PoQOracle_Supplement_stPrep
import Definitions.Def_QAdvFew_PoQOracle_Supplement_UCirc

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle.Supplement

/-- The state `|ϕ_x⟩ = V_x|0⟩` of a level-`t` sample (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, §5.1, p. 32 (PDF p. 34)). -/
noncomputable def phiD {t : ℕ} (s : DSample t) (x : Bits t) : QState (4 * t) :=
  fun w => (s.2.2.1 x : Matrix (Bits (4 * t)) (Bits (4 * t)) ℂ) w (fun _ => false)

/-- The **claw state** `|c_{x,y}⟩ ∝ |u_{x,y}⟩ + |v_{x,y}⟩` (§5.1, p. 33 (PDF p. 35): "Note that the
normalization differs depending on whether `u_{x,y} = v_{x,y}`"), with `RO_t(x, y) = (u, v)`:
`(|u⟩ + |v⟩)/√(2 + 2·1[u = v])`, which is `|u⟩` when `u = v`. -/
noncomputable def clawD {t : ℕ} (s : DSample t) (x : Bits t) (y : Bits (4 * t)) :
    QState (6 * t) :=
  fun z =>
    ((if z = (s.1 (x, y)).1 then 1 else 0) + (if z = (s.1 (x, y)).2 then 1 else 0)) /
      (Real.sqrt (2 + 2 * (if (s.1 (x, y)).1 = (s.1 (x, y)).2 then 1 else 0)) : ℂ)

/-- The fixed purification of `σ_t = 2^{−t} Σ_x |x⟩⟨x| ⊗ |ϕ_x⟩⟨ϕ_x|` (§5.1, p. 33, item 3) on
`(t + 4t) + 4t` qubits: `Σ_x 2^{−t/2} |x⟩|ϕ_x⟩ ⊗ |x 0^{3t}⟩`.

**Formalization Note** The paper fixes "any" purification; with `W^SG_t` Haar-distributed the law of
`SG_t` does not depend on the choice, since two purifications on the same register differ by a
unitary on the purifying register. -/
noncomputable def sigmaPur {t : ℕ} (s : DSample t) : QState ((t + 4 * t) + 4 * t) :=
  fun z =>
    let x : Bits t := lft (lft z)
    let w : Bits (4 * t) := rgt (lft z)
    let p : Bits (4 * t) := rgt z
    ((Real.sqrt (2 ^ t))⁻¹ : ℂ) * phiD s x w *
      (if p = (fun j : Fin (4 * t) => if h : (j : ℕ) < t then x ⟨j, h⟩ else false) then 1 else 0)

/-- The fixed purification of `ρ_x = 2^{−4t} Σ_y |y⟩⟨y| ⊗ |c_{x,y}⟩⟨c_{x,y}|` (§5.1, p. 33, item 4)
on `(4t + 6t) + (4t + 1)` qubits: `Σ_y 2^{−2t} |y⟩|c_{x,y}⟩ ⊗ |y 0⟩`. -/
noncomputable def rhoPur {t : ℕ} (s : DSample t) (x : Bits t) :
    QState ((4 * t + 6 * t) + (4 * t + 1)) :=
  fun z =>
    let y : Bits (4 * t) := lft (lft z)
    let c : Bits (6 * t) := rgt (lft z)
    let p : Bits (4 * t + 1) := rgt z
    ((Real.sqrt (2 ^ (4 * t)))⁻¹ : ℂ) * clawD s x y c *
      (if p = (fun j : Fin (4 * t + 1) => if h : (j : ℕ) < 4 * t then y ⟨j, h⟩ else false) then 1 else 0)

/-- `SG_t = S^{W^SG_t}_{σ_t}` (§5.1, p. 33: "`SG_t` will be a state preparation unitary for `σ_t`
indexed by `W^SG_t`"), on `1 + ((t + 4t) + 4t)` qubits. -/
noncomputable def sgD {t : ℕ} (s : DSample t) :
    Matrix (Bits (1 + ((t + 4 * t) + 4 * t))) (Bits (1 + ((t + 4 * t) + 4 * t))) ℂ :=
  stPrepU (sigmaPur s) (s.2.1 : Matrix (Bits (4 * t)) (Bits (4 * t)) ℂ)

/-- `Expand_t = Σ_x |x⟩⟨x| ⊗ S^{W^Expand_{t,x}}_{ρ_x}` (§5.1, p. 33), on
`t + (1 + ((4t + 6t) + (4t + 1)))` qubits. -/
noncomputable def expandD {t : ℕ} (s : DSample t) :
    Matrix (Bits (t + (1 + ((4 * t + 6 * t) + (4 * t + 1)))))
      (Bits (t + (1 + ((4 * t + 6 * t) + (4 * t + 1))))) ℂ :=
  fun y z =>
    if lft y = lft z then
      stPrepU (rhoPur s (lft y)) (s.2.2.2 (lft y) : Matrix (Bits (4 * t + 1)) (Bits (4 * t + 1)) ℂ)
        (rgt y) (rgt z)
    else 0

/-- `Mix_t = Σ_{x,y} |x,y⟩⟨x,y| ⊗ (|ϕ_x⟩⟨ϕ_x| ⊗ S_{|u_{x,y}, v_{x,y}⟩} + (I − |ϕ_x⟩⟨ϕ_x|) ⊗ I)`
(§5.1, p. 33), on `((t + 4t) + 4t) + (1 + (6t + 6t))` qubits: registers `x`, `y`, the `|ϕ_x⟩`
register, and the register of `S_{|u,v⟩}` (flag and `12t` qubits). -/
noncomputable def mixD {t : ℕ} (s : DSample t) :
    Matrix (Bits (((t + 4 * t) + 4 * t) + (1 + (6 * t + 6 * t))))
      (Bits (((t + 4 * t) + 4 * t) + (1 + (6 * t + 6 * t)))) ℂ :=
  fun y z =>
    let xy : Bits (t + 4 * t) := lft (lft y)
    let xy' : Bits (t + 4 * t) := lft (lft z)
    let w : Bits (4 * t) := rgt (lft y)
    let w' : Bits (4 * t) := rgt (lft z)
    let f : Bits (1 + (6 * t + 6 * t)) := rgt y
    let f' : Bits (1 + (6 * t + 6 * t)) := rgt z
    let x : Bits t := lft xy
    let uv : Bits (6 * t + 6 * t) := Fin.append (s.1 (x, rgt xy)).1 (s.1 (x, rgt xy)).2
    if xy = xy' then
      (if w = w' ∧ f = f' then 1 else 0) +
        phiD s x w * star (phiD s x w') *
          (stPrep (QAdvFew.PoQOracle.basisState uv) f f' - (if f = f' then 1 else 0))
    else 0

/-- The arities of the components `(SG, Expand, Mix)` = components `0, 1, 2`; other components have
arity `0`. -/
def arD : ℕ → ℕ → ℕ
  | 0, t => 1 + ((t + 4 * t) + 4 * t)
  | 1, t => t + (1 + ((4 * t + 6 * t) + (4 * t + 1)))
  | 2, t => ((t + 4 * t) + 4 * t) + (1 + (6 * t + 6 * t))
  | _, _ => 0

/-- The unitary oracle `O = (SG, Expand, Mix)` of a sample of all levels (§5.1, pp. 32–33,
PDF pp. 34–35: "`O = (SG, Expand, Mix) ← D` … `O_t = (SG_t, Expand_t, Mix_t)`"). Components `≥ 3`
are the identity on zero qubits. -/
noncomputable def oracleD (ω : (t : ℕ) → DSample t) : UOracle arD
  | 0, t => sgD (ω t)
  | 1, t => expandD (ω t)
  | 2, t => mixD (ω t)
  | _ + 3, _ => 1

end QAdvFew.PoQOracle.Supplement


