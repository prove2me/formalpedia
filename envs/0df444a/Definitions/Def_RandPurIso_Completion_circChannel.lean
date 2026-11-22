-- Prove2me | Definitions.Def_RandPurIso_Completion_circChannel
-- name    : RandPurIso_Completion_circChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:28:41.670639+00:00
-- url     : https://prove2.me/theorems/d843e182-d0ff-434f-b1df-24f5dbb7aa0f
-- title:
--   The channel implemented by a stateless circuit
-- statement:
--   For a circuit on $k$ data qubits and $a$ ancillas, the channel $\mathbf L(X)\to\mathbf L(Y_\perp)$ obtained by encoding $x$ as $e_{\mathrm{In}}(x)$, appending $|0^a\rangle$, running the circuit, tracing out the ancillas and reading $e_{\mathrm{Out}}(y)$ as $y$ and every other string as $\perp$. It is compared with $\Phi_K$ in Theorem 3.10 (exactly) and Lemma 3.15 (approximately).
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Theorem 3.10 and Lemma 3.15, pp. 19, 24

import Mathlib
import Definitions.Def_RandPurIso_Completion_QInstr
open Matrix

namespace RandPurIso.Completion

open ShiShallow

open Classical in
/-- **The channel implemented by a stateless circuit** (Theorem 3.10's "implementation" and Lemma
3.15's "implemented … using … gates", Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, pp. 19, 24).

Encode the input `x ∈ X` as `eIn x` on `k` data qubits, append `|0^a⟩`, run the circuit (with the
oracles' channels `Ψ`), trace out the ancillas and read the data qubits: `eOut y` gives `y`, every
other string gives `⊥`. The result is a map `L(X) → L(Y⊥)`, comparable with `Φ_K`
(`contractionChannel`). -/
noncomputable def circChannel {q : ℕ} {w : Fin q → ℕ} {k a : ℕ} {X Y : Type}
    [Fintype X] [Fintype Y] (c : List (QInstr q w (k + a)))
    (Ψ : (j : Fin q) → Matrix (Bits (w j)) (Bits (w j)) ℂ → Matrix (Bits (w j)) (Bits (w j)) ℂ)
    (eIn : X → Bits k) (eOut : Y → Bits k) (ρ : Matrix X X ℂ) : Matrix (Option Y) (Option Y) ℂ :=
  let E : Matrix (Bits (k + a)) X ℂ :=
    fun z x => if z = Fin.append (eIn x) (fun _ => false) then 1 else 0
  let σ := QInstr.evalList Ψ c (E * ρ * Eᴴ)
  fun i j => match i, j with
    | some y, some y' => ∑ α : Bits a, σ (Fin.append (eOut y) α) (Fin.append (eOut y') α)
    | none, none => ∑ α : Bits a, ∑ u : Bits k,
        if ∃ y, eOut y = u then 0 else σ (Fin.append u α) (Fin.append u α)
    | _, _ => 0

end RandPurIso.Completion


