-- Prove2me | Definitions.Def_ExactAmpDich_Circuit
-- name    : ExactAmpDich_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:29:23.025106+00:00
-- url     : https://prove2.me/theorems/d2f713a2-170a-4ee5-889f-4bdf9d6a39d2
-- title:
--   Circuits over a library, the unitary $U_C=U_m\cdots U_1$ and the amplitude $\langle a|U_C|b\rangle$
-- statement:
--   Fix a gate library $G=(U_1,\dots,U_t)$. A **gate occurrence** on $n$ wires is a gate $U_j$ together with an ordered tuple $(w_1,\dots,w_{k_j})$ of **distinct** wires in $\{0,\dots,n-1\}$; the $i$-th qubit of the gate sits on wire $w_i$. Its matrix on $(\mathbb C^2)^{\otimes n}$ has entry
--
--   $$\langle y|\,U_j[w]\,|x\rangle=\begin{cases}\langle y_{w}|U_j|x_{w}\rangle & \text{if } y_i=x_i \text{ for every wire } i\notin\{w_1,\dots,w_{k_j}\},\\ 0&\text{otherwise,}\end{cases}$$
--
--   where $y_w=(y_{w_1},\dots,y_{w_{k_j}})$. A **circuit** $C$ on $n$ wires is a finite sequence of occurrences $(U_1[w^1],\dots,U_m[w^m])$; it implements
--
--   $$U_C=U_m[w^m]\cdots U_1[w^1],$$
--
--   the first occurrence being applied first (the empty circuit implements the identity). An **input** of the amplitude problem is $(n,C,a,b)$ with $a,b\in\{0,1\}^n$ specifying all wires, and its **amplitude** is $\langle a|U_C|b\rangle$, the coefficient of $|a\rangle$ in $U_C|b\rangle$.
--
--   Every gate may act on any ordered tuple of distinct wires; there are no intermediate measurements, and one-qubit gates or inverses are available only if the library supplies them.
-- source:
--   Liu–Meng, A Dichotomy for Exact Quantum Circuit Amplitudes, STOC 2027 submission (held manuscript, sha256 40ad9c68…), §1, p.1 (PDF p.2); §1.1, p.2 (PDF p.3): "AmpZ(G)(C, a, b) = ⟨a|UC|b⟩"; App. A.1, p.18 (PDF p.19)

import Mathlib
import Definitions.Def_ExactAmpDich_Library

set_option autoImplicit false

namespace ExactAmpDich

open QAlgorithms

/-- A **gate occurrence** on `n` wires: a gate `j` of the library together with an ordered tuple
of `k j` *distinct* wires (an injective map `Fin (k j) ↪ Fin n`); the `i`-th qubit of the gate
sits on wire `w i`. Liu–Meng, §1, p.1 (PDF p.2): "Each k-qubit gate may act on any ordered tuple
of k distinct wires"; App. A.1, p.18: "an explicit sequence of occurrences, each carrying an
ordered tuple of distinct qubit positions". -/
abbrev Placement (L : Library) (n : ℕ) := Σ j : Fin L.t, Fin (L.k j) ↪ Fin n

/-- The `2ⁿ × 2ⁿ` matrix of a gate occurrence: entry `(y, x)` is `U_j (y ∘ w) (x ∘ w)` when `y`
and `x` agree on every wire outside the range of `w`, and `0` otherwise (identity on the other
wires). -/
def Placement.embed {L : Library} {n : ℕ} (p : Placement L n) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  fun y x => if ∀ i : Fin n, (∀ l, p.2 l ≠ i) → y i = x i then
    L.U p.1 (fun l => y (p.2 l)) (fun l => x (p.2 l)) else 0

/-- A **circuit** over the library on `n` wires: an explicit finite sequence of gate occurrences.
There are no intermediate measurements and no gates other than those of the library. -/
abbrev Circuit (L : Library) (n : ℕ) := List (Placement L n)

/-- The unitary `U_C = U_m ⋯ U_1` implemented by the circuit `C = (U_1, …, U_m)` on `(ℂ²)^{⊗n}`:
the first occurrence of the list is applied first. Liu–Meng, §1.1, p.2: "Let UC be the unitary on
(C2)⊗n implemented by an n-wire circuit C over the fixed library G". The empty circuit gives the
identity. -/
def Circuit.unitary {L : Library} {n : ℕ} (c : Circuit L n) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  (c.map Placement.embed).reverse.prod

/-- The **exact amplitude** `Amp_Z(G)(C, a, b) = ⟨a|U_C|b⟩` for output string `a` and input
string `b`, both in `{0,1}ⁿ`. Liu–Meng, §1.1, p.2 (PDF p.3). -/
def amplitude {L : Library} {n : ℕ} (c : Circuit L n) (a b : Qubits n) : ℂ :=
  c.unitary a b

/-- An **input** of the amplitude problem: the number of wires `n`, a circuit on `n` wires, the
output string `a` and the input string `b`. Liu–Meng, App. A.1, p.18: "Its input includes both
length-n boundary strings. Identity wires are permitted." -/
structure Input (L : Library) where
  /-- The number of wires. -/
  n : ℕ
  /-- The circuit. -/
  c : Circuit L n
  /-- The output string. -/
  a : Qubits n
  /-- The input string. -/
  b : Qubits n

/-- The amplitude `⟨a|U_C|b⟩` of an input. -/
def Input.amp {L : Library} (q : Input L) : ℂ := amplitude q.c q.a q.b

end ExactAmpDich


