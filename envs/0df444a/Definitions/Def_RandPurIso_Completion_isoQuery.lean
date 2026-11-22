-- Prove2me | Definitions.Def_RandPurIso_Completion_isoQuery
-- name    : RandPurIso_Completion_isoQuery
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:29:59.835645+00:00
-- url     : https://prove2.me/theorems/2020a72c-96fc-4f4e-a1ec-b355cf9891f8
-- title:
--   Qubit forms of $\Phi^V$, $\Phi^{\mathrm{ctrl}[V]}$ and $M^\Pi$
-- statement:
--   With $A=\{0,1\}^a$, $A_{\mathrm{pure}}=\{0,1\}^p$ and a flag qubit marking $\perp$:
--
--   1. `isoQuery V`: $\Phi^V$ for $V:A\to A\otimes A_{\mathrm{pure}}$ on $a+p+1$ qubits, input $|x,0^p,0\rangle$, output $V|x\rangle|0\rangle$, $\perp=|0^a0^p1\rangle$;
--   2. `ctrlIsoQuery V`: $\Phi^{\mathrm{ctrl}[V]}$ (Definition 3.9) on $1+(a+p+1)$ qubits, control first;
--   3. `measQueryAP`, `measQueryA`: $M^\Pi$ (Definition 3.8) for $\Pi$ on $A\otimes A_{\mathrm{pure}}$ or on $A$, the last qubit being $C$.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Definitions 3.4, 3.8, 3.9, pp. 18–19

import Mathlib
import Definitions.Def_RandPurIso_Completion_qubitChannel
import Definitions.Def_RandPurIso_Completion_coherentMeasU
import Definitions.Def_RandPurIso_Completion_ctrlMap
open Matrix

namespace RandPurIso.Completion

open ShiShallow

/-- Qubit layout of `A ⊗ A_pure ⊗ flag` with `A = {0,1}^a`, `A_pure = {0,1}^p`: the flag qubit
marks `⊥`. -/
def apEnc {a p : ℕ} (x : Bits a) (z : Bits p) (f : Bool) : Bits (a + p + 1) :=
  Fin.append (Fin.append x z) (fun _ => f)

/-- **Ordinary query `Φ^V`** to `V : A → A ⊗ A_pure` on `a + p + 1` qubits (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Definitions 3.4,
3.9): input `|x⟩|0^p⟩|0⟩`, output `V|x⟩|0⟩`, `⊥ = |0^a 0^p 1⟩`. -/
noncomputable def isoQuery {a p : ℕ} (V : Matrix (Bits a × Bits p) (Bits a) ℂ) :
    Matrix (Bits (a + p + 1)) (Bits (a + p + 1)) ℂ → Matrix (Bits (a + p + 1)) (Bits (a + p + 1)) ℂ :=
  qubitChannel V (fun x => apEnc x (zeroBits p) false) (fun xz => apEnc xz.1 xz.2 false)
    (apEnc (zeroBits a) (zeroBits p) true)

/-- **Controlled query `Φ^{ctrl[V]}`** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Definition 3.9, p. 19) on `1 + (a + p + 1)` qubits:
`ctrl[V] = |1⟩⟨1| ⊗ V + |0⟩⟨0| ⊗ (I_A ⊗ |0⟩_{A_pure})`, control qubit first, `⊥` flagged. -/
noncomputable def ctrlIsoQuery {a p : ℕ} (V : Matrix (Bits a × Bits p) (Bits a) ℂ) :
    Matrix (Bits (1 + (a + p + 1))) (Bits (1 + (a + p + 1))) ℂ →
      Matrix (Bits (1 + (a + p + 1))) (Bits (1 + (a + p + 1))) ℂ :=
  qubitChannel (ctrlMap true V (idleEmbed (fun z => if z = zeroBits p then 1 else 0)))
    (fun cx => Fin.append (fun _ => cx.1) (apEnc cx.2 (zeroBits p) false))
    (fun cxz => Fin.append (fun _ => cxz.1) (apEnc cxz.2.1 cxz.2.2 false))
    (Fin.append (fun _ => false) (apEnc (zeroBits a) (zeroBits p) true))

/-- **`M^{Π}` for `Π` on `A ⊗ A_pure`** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Definition 3.8, p. 19) on `a + p + 1` qubits, the last
qubit being `C`. -/
noncomputable def measQueryAP {a p : ℕ} (P : Matrix (Bits a × Bits p) (Bits a × Bits p) ℂ) :
    Matrix (Bits (a + p + 1)) (Bits (a + p + 1)) ℂ → Matrix (Bits (a + p + 1)) (Bits (a + p + 1)) ℂ :=
  qubitChannel (coherentMeasU P) (fun xzc => apEnc xzc.1.1 xzc.1.2 xzc.2)
    (fun xzc => apEnc xzc.1.1 xzc.1.2 xzc.2) (apEnc (zeroBits a) (zeroBits p) false)

/-- **`M^{Π}` for `Π` on `A`** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Definition 3.8, p. 19) on `a + 1` qubits, the last being `C`. -/
noncomputable def measQueryA {a : ℕ} (P : Matrix (Bits a) (Bits a) ℂ) :
    Matrix (Bits (a + 1)) (Bits (a + 1)) ℂ → Matrix (Bits (a + 1)) (Bits (a + 1)) ℂ :=
  qubitChannel (coherentMeasU P) (fun xc => Fin.append xc.1 (fun _ => xc.2))
    (fun xc => Fin.append xc.1 (fun _ => xc.2)) (zeroBits (a + 1))

end RandPurIso.Completion


