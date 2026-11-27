-- Prove2me | Definitions.Def_palomar_zf207_tm_check
-- name    : palomar_zf207_tm_check
-- status  : Definition
-- author  : @fl-39
-- created : 2026-11-26T23:28:14.849817+00:00
-- url     : https://prove2.me/theorems/a9d6901e-75e5-46eb-a6cb-9cfa2e99f36d
-- title:
--   ZF207: bit-list window simulator and register-macro checker for the 207-state machine
-- statement:
--   Defines an executable bit-list window simulator and register-machine macro checker for the literal 207-state binary Turing machine.
--
--   The transition table is encoded as a balanced binary search tree `fastRow`, and the finite tape window surrounding the head is represented as a pair of bit-lists (`List Bool`) stepped by `stepBits` and `runBits`. To accelerate decoding of the 42-bit instruction prefix (`decodeLBits`), non-modifying left-scans back to state $74$ are collapsed via `returnTo74From3` and `returnTo74From2` whenever no run of seven consecutive zeros intervenes before the sentinel bit.
--
--   On top of the instruction decoder (`resolveStep` and `reachesGoto`), the module defines executable checkers (`chkInc`, `chkZero`, `chkMove`, `chkLin2`, `chkLin4`, `chkCopy3`, `chkUnpair`, `chkPairLoop`, `chkPushR3`, `chkPopPair4`) and the 275-operation straight-line sequence `bopsChunk0`--`bopsChunk18` implementing Branch B (which constructs the $\mathcal{C}$-axioms $\rho_8$, `head1`--`head6`, and the gate formula `gateF`).
--
--   This pure-definition module allows the 19 Branch B verification chunks to be certified as independent, fast-compiling sub-theorems and imported into the main Turing machine soundness proof.
-- source:
--   James Chang, 'Nonhalting and ZF-independence for a 207-state Turing machine' (2026), Sections 2-3 (pp. 2-4)

namespace PalomarZF207TMCheck

abbrev Trans := Option (Bool × Bool × Nat) × Option (Bool × Bool × Nat)

def fastRow (q : Nat) : Trans :=
  match Nat.ble 207 q with
  | true => (none, none)
  | false =>
    (match Nat.ble 103 q with
    | false => (match Nat.ble 51 q with
      | false => (match Nat.ble 25 q with
        | false => (match Nat.ble 12 q with
          | false => (match Nat.ble 6 q with
            | false => (match Nat.ble 3 q with
              | false => (match Nat.ble 1 q with | false => (some (true, true, 1), some (true, true, 60)) | true => (match Nat.ble 2 q with | false => (some (true, true, 81), some (true, true, 1)) | true => (some (false, false, 2), some (true, false, 3))))
              | true => (match Nat.ble 4 q with | false => (some (false, false, 4), some (true, false, 3)) | true => (match Nat.ble 5 q with | false => (some (false, false, 6), some (true, false, 3)) | true => (some (true, true, 7), some (false, false, 5)))))
            | true => (match Nat.ble 9 q with
              | false => (match Nat.ble 7 q with | false => (some (false, false, 9), some (true, false, 3)) | true => (match Nat.ble 8 q with | false => (some (false, true, 7), some (false, true, 10)) | true => (some (false, true, 13), some (true, true, 12))))
              | true => (match Nat.ble 10 q with | false => (some (false, false, 14), some (true, false, 3)) | true => (match Nat.ble 11 q with | false => (some (false, false, 15), some (false, true, 10)) | true => (some (false, true, 16), some (true, true, 17))))))
          | true => (match Nat.ble 18 q with
            | false => (match Nat.ble 15 q with
              | false => (match Nat.ble 13 q with | false => (some (false, false, 78), some (true, false, 30)) | true => (match Nat.ble 14 q with | false => (some (false, false, 45), some (false, true, 21)) | true => (some (false, false, 22), some (true, false, 3))))
              | true => (match Nat.ble 16 q with | false => (some (true, false, 2), some (false, false, 2)) | true => (match Nat.ble 17 q with | false => (some (false, true, 23), some (false, true, 31)) | true => (some (false, true, 83), some (false, false, 94)))))
            | true => (match Nat.ble 21 q with
              | false => (match Nat.ble 19 q with | false => (some (false, true, 27), some (true, true, 28)) | true => (match Nat.ble 20 q with | false => (some (false, true, 29), some (true, true, 30)) | true => (some (false, true, 23), some (false, true, 56))))
              | true => (match Nat.ble 23 q with
                | false => (match Nat.ble 22 q with | false => (some (false, true, 32), some (true, true, 21)) | true => (some (false, false, 33), some (true, false, 3)))
                | true => (match Nat.ble 24 q with | false => (some (false, false, 34), some (false, true, 1)) | true => (some (false, true, 35), some (true, true, 24)))))))
        | true => (match Nat.ble 38 q with
          | false => (match Nat.ble 31 q with
            | false => (match Nat.ble 28 q with
              | false => (match Nat.ble 26 q with | false => (some (false, true, 76), some (true, true, 53)) | true => (match Nat.ble 27 q with | false => (some (false, true, 37), some (false, false, 38)) | true => (some (false, true, 39), some (true, true, 40))))
              | true => (match Nat.ble 29 q with | false => (some (false, true, 41), some (true, true, 42)) | true => (match Nat.ble 30 q with | false => (some (false, true, 43), some (true, true, 44)) | true => (some (false, true, 20), some (true, true, 45)))))
            | true => (match Nat.ble 34 q with
              | false => (match Nat.ble 32 q with | false => (some (false, true, 46), some (true, true, 31)) | true => (match Nat.ble 33 q with | false => (some (false, true, 31), some (true, true, 32)) | true => (some (false, false, 68), some (true, false, 3))))
              | true => (match Nat.ble 36 q with
                | false => (match Nat.ble 35 q with | false => (some (true, true, 34), some (true, false, 2)) | true => (some (false, true, 48), some (true, true, 35)))
                | true => (match Nat.ble 37 q with | false => (some (false, true, 27), some (true, true, 19)) | true => (some (false, false, 45), some (false, true, 35))))))
          | true => (match Nat.ble 44 q with
            | false => (match Nat.ble 41 q with
              | false => (match Nat.ble 39 q with | false => (some (false, false, 5), some (true, false, 50)) | true => (match Nat.ble 40 q with | false => (some (false, true, 23), some (false, true, 24)) | true => (some (false, true, 12), some (false, false, 15))))
              | true => (match Nat.ble 42 q with | false => (some (false, true, 52), some (true, true, 53)) | true => (match Nat.ble 43 q with | false => (some (false, true, 54), some (true, true, 55)) | true => (some (false, false, 44), some (false, true, 51)))))
            | true => (match Nat.ble 47 q with
              | false => (match Nat.ble 45 q with | false => (some (false, false, 25), some (true, true, 58)) | true => (match Nat.ble 46 q with | false => (some (false, true, 43), some (true, false, 25)) | true => (some (false, true, 24), some (true, true, 46))))
              | true => (match Nat.ble 49 q with
                | false => (match Nat.ble 48 q with | false => (some (false, false, 34), some (false, true, 60)) | true => (some (false, true, 15), some (true, true, 48)))
                | true => (match Nat.ble 50 q with | false => (some (false, true, 62), some (true, true, 63)) | true => (some (false, false, 38), some (true, false, 50))))))))
      | true => (match Nat.ble 77 q with
        | false => (match Nat.ble 64 q with
          | false => (match Nat.ble 57 q with
            | false => (match Nat.ble 54 q with
              | false => (match Nat.ble 52 q with | false => (some (false, true, 21), some (true, true, 51)) | true => (match Nat.ble 53 q with | false => (some (false, false, 45), some (false, true, 48)) | true => (some (false, true, 57), some (false, false, 15))))
              | true => (match Nat.ble 55 q with | false => (some (false, true, 64), some (true, true, 65)) | true => (match Nat.ble 56 q with | false => (some (false, true, 58), some (true, true, 66)) | true => (some (false, true, 51), some (true, true, 56)))))
            | true => (match Nat.ble 60 q with
              | false => (match Nat.ble 58 q with | false => (some (false, true, 47), some (false, true, 24)) | true => (match Nat.ble 59 q with | false => (some (false, false, 27), some (true, false, 67)) | true => (some (false, false, 101), some (true, false, 29))))
              | true => (match Nat.ble 62 q with
                | false => (match Nat.ble 61 q with | false => (some (false, true, 0), some (true, true, 60)) | true => (some (true, true, 123), some (true, false, 50)))
                | true => (match Nat.ble 63 q with | false => (some (false, true, 69), some (true, true, 207)) | true => (some (false, false, 124), some (true, true, 30))))))
          | true => (match Nat.ble 70 q with
            | false => (match Nat.ble 67 q with
              | false => (match Nat.ble 65 q with | false => (some (false, true, 39), some (true, true, 59)) | true => (match Nat.ble 66 q with | false => (some (false, false, 78), some (true, true, 70)) | true => (some (false, true, 52), some (true, false, 71))))
              | true => (match Nat.ble 68 q with | false => (some (false, true, 72), some (true, true, 73)) | true => (match Nat.ble 69 q with | false => (some (false, true, 68), some (true, true, 74)) | true => (some (false, true, 75), some (true, true, 76)))))
            | true => (match Nat.ble 73 q with
              | false => (match Nat.ble 71 q with | false => (some (false, true, 78), some (true, false, 109)) | true => (match Nat.ble 72 q with | false => (some (false, false, 97), some (true, true, 53)) | true => (some (false, true, 47), some (false, true, 32))))
              | true => (match Nat.ble 75 q with
                | false => (match Nat.ble 74 q with | false => (some (false, true, 80), some (false, false, 40)) | true => (some (false, true, 49), some (true, true, 127)))
                | true => (match Nat.ble 76 q with | false => (some (false, true, 45), some (true, true, 20)) | true => (some (false, true, 100), some (true, true, 89)))))))
        | true => (match Nat.ble 90 q with
          | false => (match Nat.ble 83 q with
            | false => (match Nat.ble 80 q with
              | false => (match Nat.ble 78 q with | false => (some (false, true, 91), some (true, true, 92)) | true => (match Nat.ble 79 q with | false => (some (false, true, 72), some (true, true, 71)) | true => (some (false, true, 90), some (true, true, 117))))
              | true => (match Nat.ble 81 q with | false => (some (false, true, 94), some (true, true, 95)) | true => (match Nat.ble 82 q with | false => (some (false, true, 61), some (false, true, 1)) | true => (some (false, true, 26), some (true, true, 96)))))
            | true => (match Nat.ble 86 q with
              | false => (match Nat.ble 84 q with | false => (some (false, true, 88), some (true, true, 87)) | true => (match Nat.ble 85 q with | false => (some (true, false, 98), some (true, false, 84)) | true => (some (false, true, 18), some (true, true, 99))))
              | true => (match Nat.ble 88 q with
                | false => (match Nat.ble 87 q with | false => (some (false, true, 57), some (true, true, 57)) | true => (some (false, true, 115), some (true, true, 114)))
                | true => (match Nat.ble 89 q with | false => (some (false, true, 16), some (true, true, 206)) | true => (some (false, true, 94), some (false, false, 126))))))
          | true => (match Nat.ble 96 q with
            | false => (match Nat.ble 93 q with
              | false => (match Nat.ble 91 q with | false => (some (false, true, 101), some (true, true, 102)) | true => (match Nat.ble 92 q with | false => (some (false, true, 66), some (true, true, 55)) | true => (some (false, true, 54), some (true, true, 103))))
              | true => (match Nat.ble 94 q with | false => (some (false, true, 20), some (true, true, 104)) | true => (match Nat.ble 95 q with | false => (some (false, true, 20), some (false, false, 10)) | true => (some (false, true, 58), some (true, true, 40)))))
            | true => (match Nat.ble 99 q with
              | false => (match Nat.ble 97 q with | false => (some (false, true, 105), some (true, true, 8)) | true => (match Nat.ble 98 q with | false => (some (false, true, 90), some (true, true, 106)) | true => (some (false, false, 126), some (false, false, 84))))
              | true => (match Nat.ble 101 q with
                | false => (match Nat.ble 100 q with | false => (some (false, true, 107), some (true, true, 93)) | true => (some (false, false, 108), some (false, false, 2)))
                | true => (match Nat.ble 102 q with | false => (some (false, true, 37), some (true, true, 67)) | true => (some (false, true, 58), some (true, true, 109)))))))))
    | true => (match Nat.ble 155 q with
      | false => (match Nat.ble 129 q with
        | false => (match Nat.ble 116 q with
          | false => (match Nat.ble 109 q with
            | false => (match Nat.ble 106 q with
              | false => (match Nat.ble 104 q with | false => (some (false, true, 58), some (true, true, 110)) | true => (match Nat.ble 105 q with | false => (some (false, true, 65), some (false, false, 15)) | true => (some (false, true, 13), some (true, true, 109))))
              | true => (match Nat.ble 107 q with | false => (some (false, true, 20), some (true, true, 111)) | true => (match Nat.ble 108 q with | false => (some (false, true, 112), some (true, false, 19)) | true => (some (false, false, 36), some (true, true, 64)))))
            | true => (match Nat.ble 112 q with
              | false => (match Nat.ble 110 q with | false => (some (false, true, 37), some (true, false, 107)) | true => (match Nat.ble 111 q with | false => (some (false, true, 119), some (false, false, 15)) | true => (some (false, true, 113), some (false, false, 15))))
              | true => (match Nat.ble 114 q with
                | false => (match Nat.ble 113 q with | false => (some (false, true, 23), some (false, true, 46)) | true => (some (false, true, 47), some (false, true, 31)))
                | true => (match Nat.ble 115 q with | false => (some (false, true, 69), some (true, true, 85)) | true => (some (false, true, 124), some (true, true, 27))))))
          | true => (match Nat.ble 122 q with
            | false => (match Nat.ble 119 q with
              | false => (match Nat.ble 117 q with | false => (some (false, true, 120), some (true, true, 106)) | true => (match Nat.ble 118 q with | false => (some (false, true, 93), some (true, true, 85)) | true => (some (false, true, 82), some (true, true, 97))))
              | true => (match Nat.ble 120 q with | false => (some (false, true, 86), some (true, true, 86)) | true => (match Nat.ble 121 q with | false => (some (false, true, 16), some (true, false, 108)) | true => (some (false, true, 69), some (true, true, 100)))))
            | true => (match Nat.ble 125 q with
              | false => (match Nat.ble 123 q with | false => (some (false, true, 95), some (true, true, 107)) | true => (match Nat.ble 124 q with | false => (some (true, false, 38), some (true, false, 98)) | true => (some (false, true, 79), some (true, true, 77))))
              | true => (match Nat.ble 127 q with
                | false => (match Nat.ble 126 q with | false => (some (false, true, 118), some (true, true, 128)) | true => (some (false, false, 5), some (false, false, 126)))
                | true => (match Nat.ble 128 q with | false => (some (false, true, 125), some (true, true, 58)) | true => (some (false, true, 11), some (true, true, 36)))))))
        | true => (match Nat.ble 142 q with
          | false => (match Nat.ble 135 q with
            | false => (match Nat.ble 132 q with
              | false => (match Nat.ble 130 q with | false => (some (false, true, 18), some (true, true, 19)) | true => (match Nat.ble 131 q with | false => (some (false, true, 77), some (true, true, 86)) | true => (some (false, true, 85), some (true, true, 130))))
              | true => (match Nat.ble 133 q with | false => (some (false, true, 129), some (true, true, 131)) | true => (match Nat.ble 134 q with | false => (some (false, false, 158), some (true, true, 77)) | true => (some (false, false, 168), some (true, true, 133)))))
            | true => (match Nat.ble 138 q with
              | false => (match Nat.ble 136 q with | false => (some (false, true, 18), some (true, true, 116)) | true => (match Nat.ble 137 q with | false => (some (false, true, 135), some (true, true, 133)) | true => (some (false, true, 133), some (true, false, 172))))
              | true => (match Nat.ble 140 q with
                | false => (match Nat.ble 139 q with | false => (some (false, true, 57), some (true, true, 77)) | true => (some (false, true, 18), some (true, true, 138)))
                | true => (match Nat.ble 141 q with | false => (some (false, false, 195), some (true, true, 139)) | true => (some (false, true, 139), some (true, true, 140))))))
          | true => (match Nat.ble 148 q with
            | false => (match Nat.ble 145 q with
              | false => (match Nat.ble 143 q with | false => (some (false, true, 137), some (true, true, 134)) | true => (match Nat.ble 144 q with | false => (some (false, true, 136), some (true, true, 142)) | true => (some (false, true, 135), some (true, true, 130))))
              | true => (match Nat.ble 146 q with | false => (some (false, true, 129), some (true, true, 144)) | true => (match Nat.ble 147 q with | false => (some (false, true, 131), some (true, true, 132)) | true => (some (false, true, 144), some (true, true, 77)))))
            | true => (match Nat.ble 151 q with
              | false => (match Nat.ble 149 q with | false => (some (false, false, 146), some (true, false, 182)) | true => (match Nat.ble 150 q with | false => (some (false, true, 148), some (true, true, 57)) | true => (some (false, true, 129), some (true, true, 149))))
              | true => (match Nat.ble 153 q with
                | false => (match Nat.ble 152 q with | false => (some (false, true, 147), some (true, true, 150)) | true => (some (false, false, 173), some (true, true, 151)))
                | true => (match Nat.ble 154 q with | false => (some (false, true, 145), some (true, true, 152)) | true => (some (false, true, 143), some (true, true, 153))))))))
      | true => (match Nat.ble 181 q with
        | false => (match Nat.ble 168 q with
          | false => (match Nat.ble 161 q with
            | false => (match Nat.ble 158 q with
              | false => (match Nat.ble 156 q with | false => (some (false, true, 134), some (true, true, 154)) | true => (match Nat.ble 157 q with | false => (some (false, true, 124), some (true, true, 155)) | true => (some (false, false, 189), some (true, true, 156))))
              | true => (match Nat.ble 159 q with | false => (some (false, true, 157), some (true, true, 145)) | true => (match Nat.ble 160 q with | false => (some (false, true, 135), some (true, false, 151)) | true => (some (false, false, 182), some (true, true, 159)))))
            | true => (match Nat.ble 164 q with
              | false => (match Nat.ble 162 q with | false => (some (false, true, 137), some (true, true, 57)) | true => (match Nat.ble 163 q with | false => (some (false, true, 160), some (true, true, 161)) | true => (some (false, true, 162), some (true, true, 136))))
              | true => (match Nat.ble 166 q with
                | false => (match Nat.ble 165 q with | false => (some (false, true, 163), some (true, true, 162)) | true => (some (false, true, 158), some (true, true, 164)))
                | true => (match Nat.ble 167 q with | false => (some (false, true, 85), some (true, true, 165)) | true => (some (false, true, 141), some (true, true, 159))))))
          | true => (match Nat.ble 174 q with
            | false => (match Nat.ble 171 q with
              | false => (match Nat.ble 169 q with | false => (some (false, true, 166), some (true, true, 167)) | true => (match Nat.ble 170 q with | false => (some (false, true, 129), some (true, true, 168)) | true => (some (false, true, 63), some (true, true, 169))))
              | true => (match Nat.ble 172 q with | false => (some (false, true, 57), some (true, true, 136)) | true => (match Nat.ble 173 q with | false => (some (false, true, 146), some (true, true, 161)) | true => (some (false, true, 171), some (true, true, 172)))))
            | true => (match Nat.ble 177 q with
              | false => (match Nat.ble 175 q with | false => (some (false, true, 170), some (true, true, 173)) | true => (match Nat.ble 176 q with | false => (some (false, true, 174), some (true, true, 132)) | true => (some (false, true, 132), some (true, true, 175))))
              | true => (match Nat.ble 179 q with
                | false => (match Nat.ble 178 q with | false => (some (false, true, 129), some (true, true, 137)) | true => (some (false, true, 177), some (true, true, 160)))
                | true => (match Nat.ble 180 q with | false => (some (false, true, 147), some (true, true, 178)) | true => (some (false, true, 150), some (true, true, 179)))))))
        | true => (match Nat.ble 194 q with
          | false => (match Nat.ble 187 q with
            | false => (match Nat.ble 184 q with
              | false => (match Nat.ble 182 q with | false => (some (false, true, 152), some (true, true, 180)) | true => (match Nat.ble 183 q with | false => (some (false, true, 138), some (true, true, 144)) | true => (some (false, true, 136), some (true, true, 182))))
              | true => (match Nat.ble 185 q with | false => (some (false, true, 135), some (true, true, 177)) | true => (match Nat.ble 186 q with | false => (some (false, true, 139), some (true, true, 77)) | true => (some (false, true, 185), some (true, true, 148)))))
            | true => (match Nat.ble 190 q with
              | false => (match Nat.ble 188 q with | false => (some (false, true, 184), some (true, true, 186)) | true => (match Nat.ble 189 q with | false => (some (false, false, 204), some (true, true, 187)) | true => (some (false, true, 188), some (true, true, 186))))
              | true => (match Nat.ble 192 q with
                | false => (match Nat.ble 191 q with | false => (some (false, true, 183), some (true, true, 189)) | true => (some (false, true, 181), some (true, true, 190)))
                | true => (match Nat.ble 193 q with | false => (some (false, false, 195), some (true, true, 185)) | true => (some (false, true, 77), some (true, true, 192))))))
          | true => (match Nat.ble 200 q with
            | false => (match Nat.ble 197 q with
              | false => (match Nat.ble 195 q with | false => (some (false, true, 131), some (true, true, 186)) | true => (match Nat.ble 196 q with | false => (some (false, true, 193), some (true, true, 194)) | true => (some (false, true, 191), some (true, true, 195))))
              | true => (match Nat.ble 198 q with | false => (some (false, true, 192), some (true, true, 147)) | true => (match Nat.ble 199 q with | false => (some (false, true, 140), some (true, true, 120)) | true => (some (false, true, 121), some (false, false, 126)))))
            | true => (match Nat.ble 203 q with
              | false => (match Nat.ble 201 q with | false => (some (false, true, 122), some (true, true, 199)) | true => (match Nat.ble 202 q with | false => (some (false, true, 121), some (true, true, 200)) | true => (some (false, true, 198), some (true, true, 201))))
              | true => (match Nat.ble 205 q with
                | false => (match Nat.ble 204 q with | false => (some (false, true, 197), some (true, true, 202)) | true => (some (false, false, 188), some (true, true, 203)))
                | true => (match Nat.ble 206 q with | false => (some (false, true, 196), some (true, true, 204)) | true => (some (false, true, 176), some (true, true, 205))))))))))

def bitsToNat : List Bool → Nat
  | [] => 0
  | false :: bs => 2 * bitsToNat bs
  | true :: bs => 1 + 2 * bitsToNat bs

def natToBits : Nat → Nat → List Bool
  | 0, _ => []
  | k + 1, n => Nat.beq (n % 2) 1 :: natToBits k (n / 2)

def pB (n : Nat) : List Bool := natToBits 42 n

def allFalse : List Bool → Bool
  | [] => true
  | false :: bs => allFalse bs
  | true :: _ => false

def allTrue : List Bool → Bool
  | [] => true
  | true :: bs => allTrue bs
  | false :: _ => false

def isOneBits : List Bool → Bool
  | true :: bs => allFalse bs
  | _ => false

def beqBits : List Bool → List Bool → Bool
  | [], [] => true
  | true :: as, true :: bs => beqBits as bs
  | false :: as, false :: bs => beqBits as bs
  | _, _ => false

def popLeft : List Bool → Bool × List Bool
  | [] => (false, [])
  | b :: bs => (b, bs)

def stepBits (q : Nat) (l r : List Bool) : Option (Nat × List Bool × List Bool) :=
  match r with
  | [] => none
  | b :: rs =>
    let tr := match b with | true => (fastRow q).2 | false => (fastRow q).1
    match tr with
    | none => some (q, l, b :: rs)
    | some (w, dir, nq) =>
      match dir with
      | true => some (nq, w :: l, rs)
      | false =>
        match l with
        | [] => some (nq, [], false :: w :: rs)
        | lb :: ls => some (nq, ls, lb :: w :: rs)

def runBits (stop : Nat → Bool) :
    Nat → Nat → List Bool → List Bool → Option (Nat × List Bool × List Bool)
  | fuel, q, l, r =>
    match stop q with
    | true => some (q, l, r)
    | false =>
      match fuel with
      | 0 => none
      | fuel' + 1 =>
        match Nat.ble 207 q with
        | true => none
        | false =>
          match stepBits q l r with
          | none => none
          | some (q', l', r') => runBits stop fuel' q' l' r'

def isGadgetOrHalt (q : Nat) : Bool :=
  match Nat.ble 127 q with
  | true => Nat.ble 207 q
  | false =>
    match Nat.ble 36 q with
    | false =>
      match Nat.ble 16 q with
      | false =>
        match Nat.ble 8 q with
        | false => true
        | true => Nat.beq q 9 || Nat.beq q 10 || Nat.beq q 14 || Nat.beq q 15
      | true =>
        match Nat.ble 31 q with
        | true => true
        | false => Nat.beq q 21 || Nat.beq q 22 || Nat.beq q 24
    | true =>
      match Nat.ble 62 q with
      | false =>
        match Nat.ble 51 q with
        | false => Nat.beq q 38 || Nat.beq q 46 || Nat.beq q 48 || Nat.beq q 50
        | true => Nat.beq q 51 || Nat.beq q 56 || Nat.beq q 60 || Nat.beq q 61
      | true =>
        match Nat.ble 85 q with
        | false => Nat.beq q 68 || Nat.beq q 81 || Nat.beq q 84
        | true => Nat.beq q 98 || Nat.beq q 123 || Nat.beq q 126

def regOfSkipState (q : Nat) : Option Nat :=
  match Nat.ble 57 q with
  | true => none
  | false =>
    match Nat.ble 35 q with
    | false =>
      if Nat.beq q 21 then some 6
      else if Nat.beq q 24 then some 2
      else if Nat.beq q 31 then some 4
      else if Nat.beq q 32 then some 5
      else none
    | true =>
      if Nat.beq q 35 then some 1
      else if Nat.beq q 46 then some 3
      else if Nat.beq q 48 then some 0
      else if Nat.beq q 51 then some 7
      else if Nat.beq q 56 then some 8
      else none

def splitLastTrue : List Bool → Option (List Bool)
  | [] => none
  | b :: bs =>
    match splitLastTrue bs with
    | some xs => some (b :: xs)
    | none => if b then some [] else none

def zState : Nat → Nat
  | 0 => 3 | 1 => 4 | 2 => 6 | 3 => 9 | 4 => 14 | 5 => 22 | _ => 33

def no7zeros : Nat → List Bool → Bool
  | k, [] => Nat.ble k 6
  | _, true :: bs => no7zeros 0 bs
  | k, false :: bs => if Nat.ble 6 k then false else no7zeros (k + 1) bs

def okFrom2 : List Bool → Bool
  | [] => true
  | true :: bs => no7zeros 0 bs
  | false :: bs => okFrom2 bs

def returnTo74From3 (l r : List Bool) : Option (List Bool × List Bool) :=
  match r with
  | [] => none
  | b :: rs =>
    match splitLastTrue l with
    | some xs =>
      match no7zeros 0 (b :: xs) with
      | true => some ([true], xs.reverse ++ b :: rs)
      | false =>
        match runBits (fun x => Nat.beq x 74) 160 3 l (b :: rs) with
        | some (_, l', r') => some (l', r')
        | none => none
    | none =>
      match runBits (fun x => Nat.beq x 74) 160 3 l (b :: rs) with
      | some (_, l', r') => some (l', r')
      | none => none

def returnTo74From2 (l r : List Bool) : Option (List Bool × List Bool) :=
  match r with
  | [] => none
  | b :: rs =>
    match splitLastTrue l with
    | some xs =>
      match okFrom2 (b :: xs) with
      | true => some ([true], xs.reverse ++ b :: rs)
      | false =>
        match runBits (fun x => Nat.beq x 74) 160 2 l (b :: rs) with
        | some (_, l', r') => some (l', r')
        | none => none
    | none =>
      match runBits (fun x => Nat.beq x 74) 160 2 l (b :: rs) with
      | some (_, l', r') => some (l', r')
      | none => none

inductive DecodeAct where
  | goto (next : List Bool)
  | inc (k : Nat) (next : List Bool)
  | dec (k : Nat) (nz z : List Bool)
  | halt
  | fail

def finishEraseBits (q : Nat) (l r : List Bool) : Option (List Bool) :=
  match runBits (fun x => Nat.beq x 10) 100 q l r with
  | none => none
  | some (_, l4, r4) =>
    match allTrue r4 with
    | false => none
    | true =>
      let (lb, ls) := popLeft l4
      match returnTo74From2 ls (lb :: List.replicate r4.length false) with
      | some (l5, r5) =>
        match isOneBits l5 && Nat.beq r5.length 42 with
        | true => some r5
        | false => none
      | none => none

def decodeLBits (pref : List Bool) : DecodeAct :=
  match runBits isGadgetOrHalt 100 74 [true] pref with
  | none => .fail
  | some (q1, l1, r1) =>
    if Nat.ble 207 q1 then .halt
    else if Nat.beq q1 34 then
      match allFalse r1 with
      | false => .fail
      | true =>
        let (lb1, ls1) := popLeft l1
        match returnTo74From3 ls1 (lb1 :: List.replicate r1.length true) with
        | none => .fail
        | some (l2_0, r2_0) =>
          match runBits (fun q => (regOfSkipState q).isSome) 100 74 l2_0 r2_0 with
          | none => .fail
          | some (q2, l2, r2) =>
            match regOfSkipState q2, allTrue r2 with
            | some k, true =>
              let (lb2, ls2) := popLeft l2
              match returnTo74From3 ls2 (lb2 :: List.replicate r2.length true) with
              | none => .fail
              | some (l3_0, r3_0) =>
                match runBits (fun q => Nat.beq q 60 || Nat.beq q 1) 100 74 l3_0 r3_0 with
                | none => .fail
                | some (q3, l3, r3) =>
                  match allTrue r3 with
                  | false => .fail
                  | true =>
                    match l3 with
                    | false :: false :: l3' =>
                      if Nat.beq q3 60 then
                        match finishEraseBits 38 l3' (false :: false :: List.replicate r3.length true) with
                        | some pn => .inc k pn
                        | none => .fail
                      else if Nat.beq q3 1 then
                        let (lb3, ls3) := popLeft l3'
                        match finishEraseBits 38 l3' (false :: false :: List.replicate r3.length true),
                              finishEraseBits 126 ls3 (lb3 :: false :: true :: List.replicate r3.length true) with
                        | some pnz, some pz => .dec k pnz pz
                        | _, _ => .fail
                      else .fail
                    | _ => .fail
            | _, _ => .fail
    else
      match runBits (fun q => Nat.beq q 74 || Nat.beq q 7) 150 q1 l1 r1 with
      | none => .fail
      | some (qg, lg, rg) =>
        if Nat.beq qg 74 then
          match isOneBits lg && Nat.beq rg.length 42 with
          | true => .goto rg
          | false => .fail
        else if Nat.beq qg 7 then
          match allFalse rg with
          | true =>
            let (lbg, lsg) := popLeft lg
            match returnTo74From2 lsg (lbg :: List.replicate rg.length false) with
            | some (l5, r5) =>
              match isOneBits l5 && Nat.beq r5.length 42 with
              | true => .goto r5
              | false => .fail
            | none => .fail
          | false =>
            match runBits (fun q => Nat.beq q 74) 150 7 lg rg with
            | some (_, l5, r5) =>
              match isOneBits l5 && Nat.beq r5.length 42 with
              | true => .goto r5
              | false => .fail
            | none => .fail
        else .fail

def resolveGoto : Nat → List Bool → List Bool
  | 0, p => p
  | fuel + 1, p =>
    match decodeLBits p with
    | .goto p' => resolveGoto fuel p'
    | _ => p

def reachesGoto : Nat → List Bool → List Bool → Bool
  | 0, a, b => beqBits a b
  | fuel + 1, a, b =>
    match beqBits a b with
    | true => true
    | false =>
      match decodeLBits a with
      | .goto a' => reachesGoto fuel a' b
      | _ => false

inductive RegInstr where
  | inc (k : Nat) (next : List Bool)
  | dec (k : Nat) (nz z : List Bool)

def resolveStep : Nat → List Bool → Option (List Bool × RegInstr)
  | 0, _ => none
  | fuel + 1, p =>
    match decodeLBits p with
    | .goto p' => resolveStep fuel p'
    | .inc k pn => some (p, .inc k pn)
    | .dec k pnz pz => some (p, .dec k pnz pz)
    | _ => none

def chkInc (p : List Bool) (r : Nat) : Option (List Bool) :=
  match resolveStep 25 p with
  | some (_, .inc k pn) => if Nat.beq k r then some pn else none
  | _ => none

def chkIncN : Nat → List Bool → Nat → Option (List Bool)
  | 0, p, _ => some p
  | k + 1, p, r =>
    match chkInc p r with
    | some p' => chkIncN k p' r
    | none => none

def chkZero (p : List Bool) (r : Nat) : Option (List Bool) :=
  match resolveStep 25 p with
  | some (p0, .dec k pnz pz) => if Nat.beq k r && reachesGoto 25 pnz p0 then some pz else none
  | _ => none

def chkMove (p : List Bool) (dst src : Nat) : Option (List Bool) :=
  match resolveStep 25 p with
  | some (p0, .dec k pnz pz) =>
    if Nat.beq k src then
      match chkInc pnz dst with
      | some p2 => if reachesGoto 25 p2 p0 then some pz else none
      | none => none
    else none
  | _ => none

def chkLin2 (p : List Bool) (src d1 d2 : Nat) : Option (List Bool) :=
  match resolveStep 25 p with
  | some (p0, .dec k pnz pz) =>
    if Nat.beq k src then
      match resolveStep 25 pnz with
      | some (_, .inc k1 p1) =>
        if Nat.beq k1 d1 then
          match chkInc p1 d2 with
          | some p2 => if reachesGoto 25 p2 p0 then some pz else none
          | none => none
        else if Nat.beq k1 d2 then
          match chkInc p1 d1 with
          | some p2 => if reachesGoto 25 p2 p0 then some pz else none
          | none => none
        else none
      | _ => none
    else none
  | _ => none

def chkLin4 (p : List Bool) (dst src : Nat) : Option (List Bool) :=
  match resolveStep 25 p with
  | some (p0, .dec k pnz pz) =>
    if Nat.beq k src then
      match chkIncN 4 pnz dst with
      | some p2 => if reachesGoto 25 p2 p0 then some pz else none
      | none => none
    else none
  | _ => none

def chkCopy3 (p : List Bool) (src : Nat) : Option (List Bool) :=
  match chkLin2 p src 2 8 with
  | some p1 => chkMove p1 src 8
  | none => none

def chkUnpairLoop (p : List Bool) (src : Nat) : Option (List Bool) :=
  match resolveStep 25 p with
  | some (p0, .dec k pnz pz) =>
    if Nat.beq k src then
      match chkInc pnz 5 with
      | some p1 =>
        match resolveStep 25 p1 with
        | some (_, .dec k2 pnz2 pz2) =>
          if Nat.beq k2 8 && reachesGoto 25 pnz2 p0 then
            match chkMove pz2 8 5 with
            | some p3 => if reachesGoto 25 p3 p0 then some pz else none
            | none => none
          else none
        | _ => none
      | none => none
    else none
  | _ => none

def chkUnpair (p : List Bool) (src dst : Nat) : Option (List Bool) :=
  match chkUnpairLoop p src with
  | some p1 =>
    match chkMove p1 src 5 with
    | some p2 => chkMove p2 dst 8
    | none => none
  | none => none

def chkPairLoop (p : List Bool) : Option (List Bool) :=
  match resolveStep 25 p with
  | some (p0, .dec k pnz pz) =>
    if Nat.beq k 8 then
      match chkInc pnz 5 with
      | some p1 =>
        match chkMove p1 2 8 with
        | some p2 =>
          match chkLin2 p2 2 5 8 with
          | some p3 => if reachesGoto 25 p3 p0 then some pz else none
          | none => none
        | none => none
      | none => none
    else none
  | _ => none

def chkPushR3 (p : List Bool) : Option (List Bool) :=
  match chkMove p 8 2 with
  | some p1 =>
    match chkMove p1 2 0 with
    | some p2 =>
      match chkLin2 p2 2 5 8 with
      | some p3 =>
        match chkPairLoop p3 with
        | some p4 => chkMove p4 0 5
        | none => none
      | none => none
    | none => none
  | none => none

def chkPopPair4 (p : List Bool) : Option (List Bool) :=
  match chkUnpairLoop p 0 with
  | some p1 =>
    match chkMove p1 0 5 with
    | some p2 =>
      match chkLin2 p2 2 5 8 with
      | some p3 =>
        match chkPairLoop p3 with
        | some p4 => chkLin4 p4 2 5
        | none => none
      | none => none
    | none => none
  | none => none

inductive BOp where
  | pushR3 | popPair4 | copy3_4 | copy3_5 | copy3_8 | unpair2_8 | unpair2_4 | inc3 (k : Nat)

def chkBOp (p : List Bool) : BOp → Option (List Bool)
  | .pushR3 => chkPushR3 p
  | .popPair4 => chkPopPair4 p
  | .copy3_4 => chkCopy3 p 3
  | .copy3_5 => chkCopy3 p 4
  | .copy3_8 => chkCopy3 p 7
  | .unpair2_8 => chkUnpair p 1 7
  | .unpair2_4 => chkUnpair p 1 3
  | .inc3 k => chkIncN k p 2

def chkBOps : List Bool → List BOp → Option (List Bool)
  | p, [] => some p
  | p, op :: ops =>
    match chkBOp p op with
    | some p' => chkBOps p' ops
    | none => none

def chkBOpsTo (p : List Bool) (ops : List BOp) (target : List Bool) : Bool :=
  match chkBOps p ops with
  | some p' => reachesGoto 25 p' target
  | none => false

def bopsChunk0 : List BOp := [.pushR3, .copy3_8, .pushR3, .copy3_4, .popPair4, .inc3 2, .unpair2_8, .pushR3, .copy3_8, .pushR3, .copy3_4, .popPair4, .unpair2_4, .pushR3, .copy3_4]
def bopsChunk1 : List BOp := [.popPair4, .pushR3, .copy3_4, .pushR3, .copy3_8, .popPair4, .pushR3, .copy3_5, .pushR3, .copy3_8, .popPair4, .popPair4, .popPair4, .pushR3, .copy3_8]
def bopsChunk2 : List BOp := [.pushR3, .copy3_4, .popPair4, .inc3 2, .pushR3, .inc3 1, .popPair4, .pushR3, .copy3_4, .popPair4, .inc3 2, .pushR3, .inc3 1, .popPair4, .pushR3]
def bopsChunk3 : List BOp := [.copy3_8, .popPair4, .pushR3, .copy3_8, .pushR3, .copy3_5, .popPair4, .inc3 2, .pushR3, .copy3_4, .popPair4, .inc3 2, .pushR3, .copy3_8, .pushR3]
def bopsChunk4 : List BOp := [.copy3_4, .popPair4, .inc3 2, .pushR3, .copy3_5, .popPair4, .inc3 2, .popPair4, .pushR3, .copy3_8, .pushR3, .copy3_4, .popPair4, .inc3 1, .pushR3]
def bopsChunk5 : List BOp := [.copy3_8, .pushR3, .copy3_5, .popPair4, .inc3 3, .pushR3, .copy3_5, .pushR3, .copy3_4, .popPair4, .inc3 1, .popPair4, .popPair4, .pushR3, .copy3_8]
def bopsChunk6 : List BOp := [.pushR3, .copy3_4, .popPair4, .inc3 3, .pushR3, .copy3_5, .pushR3, .copy3_8, .popPair4, .inc3 1, .pushR3, .copy3_5, .pushR3, .copy3_4, .popPair4]
def bopsChunk7 : List BOp := [.inc3 1, .popPair4, .popPair4, .pushR3, .copy3_8, .pushR3, .copy3_4, .popPair4, .inc3 3, .pushR3, .inc3 1, .popPair4, .pushR3, .copy3_4, .popPair4]
def bopsChunk8 : List BOp := [.inc3 2, .pushR3, .inc3 1, .popPair4, .pushR3, .copy3_5, .pushR3, .copy3_4, .popPair4, .inc3 2, .pushR3, .copy3_5, .pushR3, .copy3_8, .popPair4]
def bopsChunk9 : List BOp := [.pushR3, .copy3_4, .popPair4, .inc3 2, .pushR3, .copy3_8, .pushR3, .copy3_4, .popPair4, .inc3 2, .popPair4, .popPair4, .pushR3, .copy3_8, .pushR3]
def bopsChunk10 : List BOp := [.copy3_4, .popPair4, .inc3 3, .pushR3, .copy3_8, .pushR3, .copy3_4, .popPair4, .inc3 3, .pushR3, .copy3_5, .popPair4, .inc3 2, .popPair4, .pushR3]
def bopsChunk11 : List BOp := [.copy3_8, .pushR3, .copy3_4, .popPair4, .inc3 1, .pushR3, .copy3_8, .pushR3, .copy3_4, .popPair4, .inc3 1, .pushR3, .copy3_5, .popPair4, .inc3 2]
def bopsChunk12 : List BOp := [.popPair4, .pushR3, .copy3_8, .pushR3, .copy3_5, .popPair4, .inc3 1, .pushR3, .copy3_5, .pushR3, .copy3_5, .pushR3, .copy3_4, .popPair4, .inc3 1]
def bopsChunk13 : List BOp := [.pushR3, .copy3_5, .pushR3, .copy3_8, .popPair4, .inc3 1, .popPair4, .pushR3, .copy3_5, .popPair4, .inc3 2, .pushR3, .copy3_5, .pushR3, .copy3_5]
def bopsChunk14 : List BOp := [.pushR3, .copy3_8, .pushR3, .copy3_5, .popPair4, .inc3 1, .pushR3, .inc3 1, .popPair4, .popPair4, .pushR3, .copy3_8, .popPair4, .inc3 2, .pushR3]
def bopsChunk15 : List BOp := [.inc3 1, .popPair4, .popPair4, .pushR3, .copy3_8, .popPair4, .inc3 2, .popPair4, .pushR3, .copy3_4, .popPair4, .inc3 2, .pushR3, .inc3 1, .popPair4]
def bopsChunk16 : List BOp := [.popPair4, .pushR3, .copy3_4, .popPair4, .inc3 2, .pushR3, .inc3 1, .popPair4, .popPair4, .pushR3, .copy3_8, .popPair4, .inc3 2, .pushR3, .copy3_5]
def bopsChunk17 : List BOp := [.pushR3, .copy3_8, .pushR3, .copy3_5, .popPair4, .inc3 1, .popPair4, .pushR3, .inc3 1, .popPair4, .popPair4, .pushR3, .copy3_5, .popPair4, .inc3 2]
def bopsChunk18 : List BOp := [.popPair4, .popPair4, .pushR3, .inc3 1, .popPair4]

end PalomarZF207TMCheck


